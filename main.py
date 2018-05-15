from PyQt4 import QtCore, QtGui, QtWebKit, QtNetwork, uic
from obspy import read_inventory, read_events, UTCDateTime, Stream, read
from obspy.clients.fdsn.client import Client
from obspy.clients.fdsn.header import FDSNException
import functools
import os
import shutil
import re
import pyqtgraph as pg
import json
import pyasdf
import itertools

from seisds import SeisDB
from DateAxisItem import DateAxisItem

import pandas as pd
import numpy as np
from query_input_yes_no import query_yes_no
import sys

from sqlalchemy import create_engine
from sqlalchemy import and_, or_
from sqlalchemy.orm import sessionmaker
from sqlalchemy import func

from waveforms_db import Waveforms

from collections import defaultdict

# load in Qt Designer UI files
qc_events_ui = "qc_events.ui"
select_stacomp_dialog_ui = "select_stacomp_dialog.ui"

Ui_MainWindow, QtBaseClass = uic.loadUiType(qc_events_ui)
Ui_SelectDialog, QtBaseClass = uic.loadUiType(select_stacomp_dialog_ui)

STATION_VIEW_ITEM_TYPES = {
    "FILE": 0,
    "NETWORK": 1,
    "STATION": 2,
    "CHANNEL": 3,
    "STN_INFO": 4,
    "CHAN_INFO": 5}


class selectionDialog(QtGui.QDialog):
    '''
    Select all functionality is modified from Brendan Abel & dbc from their
    stackoverflow communication Feb 24th 2016:
    http://stackoverflow.com/questions/35611199/creating-a-toggling-check-all-checkbox-for-a-listview
    '''

    def __init__(self, parent=None, sta_list=None, chan_list=None):
        QtGui.QDialog.__init__(self, parent)
        self.selui = Ui_SelectDialog()
        self.selui.setupUi(self)
        # self.setWindowTitle('Selection Dialog')

        # Set all check box to checked
        # self.selui.check_all.setChecked(True)
        self.selui.check_all.clicked.connect(self.selectAllCheckChanged)

        # add stations to station select items
        self.sta_model = QtGui.QStandardItemModel(self.selui.StaListView)

        self.sta_list = sta_list
        for sta in self.sta_list:
            item = QtGui.QStandardItem(sta)
            item.setCheckable(True)

            self.sta_model.appendRow(item)

        self.selui.StaListView.setModel(self.sta_model)
        # connect to method to update stae of select all checkbox
        self.selui.StaListView.clicked.connect(self.listviewCheckChanged)

        # add channels to channel select items
        self.chan_model = QtGui.QStandardItemModel(self.selui.ChanListView)

        self.chan_list = chan_list
        for chan in self.chan_list:
            item = QtGui.QStandardItem(chan)
            item.setCheckable(True)

            self.chan_model.appendRow(item)

        self.selui.ChanListView.setModel(self.chan_model)

    def selectAllCheckChanged(self):
        ''' updates the listview based on select all checkbox '''
        sta_model = self.selui.StaListView.model()
        for index in range(sta_model.rowCount()):
            item = sta_model.item(index)
            if item.isCheckable():
                if self.selui.check_all.isChecked():
                    item.setCheckState(QtCore.Qt.Checked)
                else:
                    item.setCheckState(QtCore.Qt.Unchecked)

    def listviewCheckChanged(self):
        ''' updates the select all checkbox based on the listview '''
        sta_model = self.selui.StaListView.model()
        items = [sta_model.item(index) for index in range(sta_model.rowCount())]

        if all(item.checkState() == QtCore.Qt.Checked for item in items):
            self.selui.check_all.setTristate(False)
            self.selui.check_all.setCheckState(QtCore.Qt.Checked)
        elif any(item.checkState() == QtCore.Qt.Checked for item in items):
            self.selui.check_all.setTristate(True)
            self.selui.check_all.setCheckState(QtCore.Qt.PartiallyChecked)
        else:
            self.selui.check_all.setTristate(False)
            self.selui.check_all.setCheckState(QtCore.Qt.Unchecked)

    def getSelected(self):
        select_networks = set()
        select_stations = []
        select_channels = []
        i = 0
        while self.sta_model.item(i):
            if self.sta_model.item(i).checkState():
                select_networks.add(str(self.sta_model.item(i).text()).split('.')[0])
                select_stations.append(str(self.sta_model.item(i).text()).split('.')[1])
            i += 1
        i = 0
        while self.chan_model.item(i):
            if self.chan_model.item(i).checkState():
                select_channels.append(str(self.chan_model.item(i).text()))
            i += 1

        # Return Selected stations and selected channels
        return (list(select_networks), select_stations, select_channels)


class PandasModel(QtCore.QAbstractTableModel):
    """
    Class to populate a table view with a pandas dataframe
    """

    def __init__(self, data, cat_nm=None, parent=None):
        QtCore.QAbstractTableModel.__init__(self, parent)
        self._data = np.array(data.values)
        self._cols = data.columns
        self.r, self.c = np.shape(self._data)

        self.cat_nm = cat_nm

        # Column headers for tables
        self.cat_col_header = ['Event ID', 'Time (UTC Timestamp)', 'Lat (dd)', 'Lon  (dd)',
                               'Depth (km)', 'Mag', 'Time (UTC)', 'Julian Day']

    def rowCount(self, parent=None):
        return self.r

    def columnCount(self, parent=None):
        return self.c

    def data(self, index, role=QtCore.Qt.DisplayRole):

        if index.isValid():
            if role == QtCore.Qt.DisplayRole:
                return self._data[index.row(), index.column()]
        return None

    def headerData(self, p_int, orientation, role):
        if role == QtCore.Qt.DisplayRole:
            if orientation == QtCore.Qt.Horizontal:
                if not self.cat_nm == None:
                    return self.cat_col_header[p_int]
                elif not self.pick_nm == None:
                    return self.pick_col_header[p_int]
            elif orientation == QtCore.Qt.Vertical:
                return p_int
        return None


class TableDialog(QtGui.QDialog):
    """
    Class to create a separate child window to display the event catalogue
    """

    def __init__(self, parent=None, cat_df=None):
        super(TableDialog, self).__init__(parent)

        self.cat_df = cat_df

        self.initUI()

    def initUI(self):
        self.layout = QtGui.QVBoxLayout(self)

        self.cat_event_table_view = QtGui.QTableView()

        self.cat_event_table_view.setSelectionBehavior(QtGui.QAbstractItemView.SelectRows)

        self.layout.addWidget(self.cat_event_table_view)

        self.setLayout(self.layout)

        # Populate the tables using the custom Pandas table class
        self.cat_model = PandasModel(self.cat_df, cat_nm=True)

        self.cat_event_table_view.setModel(self.cat_model)

        self.setWindowTitle('EQ Catalogue')
        self.show()


class DataAvailPlot(QtGui.QDialog):
    '''
    Dialog for Data Availablity plot
    '''

    def __init__(self, parent=None, sta_list=None, chan_list=None, rec_int_dict=None):
        super(DataAvailPlot, self).__init__(parent)
        self.setWindowTitle('Data Availability Plot')

        self.rec_int_dict = rec_int_dict
        self.sta_list = sta_list
        self.chan_list = chan_list

        self.initUI()
        self.plot_data()

    def initUI(self):
        vbox = QtGui.QVBoxLayout()
        self.setLayout(vbox)

        self.data_avail_graph_view = pg.GraphicsLayoutWidget()

        vbox.addWidget(self.data_avail_graph_view)

        self.show()

    def dispMousePos(self, pos):
        # Display current mouse coords if over the scatter plot area as a tooltip
        try:
            x_coord = UTCDateTime(self.plot.vb.mapSceneToView(pos).toPoint().x()).ctime()
            self.time_tool = self.plot.setToolTip(x_coord)
        except:
            pass

    def plot_data(self):
        # Launch the custom station/component selection dialog
        sel_dlg = selectionDialog(parent=self, sta_list=self.sta_list, chan_list=self.chan_list)
        if sel_dlg.exec_():
            select_sta, select_comp = sel_dlg.getSelected()

            enum_sta = list(enumerate(select_sta))
            # rearrange dict
            sta_id_dict = dict([(b, a) for a, b in enum_sta])

            y_axis_string = pg.AxisItem(orientation='left')
            y_axis_string.setTicks([enum_sta])

            def get_sta_id(sta):
                return (sta_id_dict[sta])

            # Set up the plotting area
            self.plot = self.data_avail_graph_view.addPlot(0, 0,
                                                           axisItems={'bottom': DateAxisItem(orientation='bottom',
                                                                                             utcOffset=0),
                                                                      'left': y_axis_string})
            self.plot.setMouseEnabled(x=True, y=False)
            # When Mouse is moved over plot print the data coordinates
            self.plot.scene().sigMouseMoved.connect(self.dispMousePos)

            rec_midpoints = []
            sta_ids = []
            diff_frm_mid_list = []

            # iterate through stations
            for stn_key, chan_dict in self.rec_int_dict.iteritems():
                if not stn_key in select_sta:
                    continue
                # iterate through channels
                for chan_key, rec_list in chan_dict.iteritems():
                    if not chan_key in select_comp:
                        continue
                    # iterate through gaps list
                    for rec_entry in rec_list:
                        diff_frm_mid = (rec_entry['rec_end'] - rec_entry['rec_start']) / 2.0

                        diff_frm_mid_list.append(diff_frm_mid)

                        rec_midpoints.append(rec_entry['rec_start'] + diff_frm_mid)
                        sta_ids.append(get_sta_id(stn_key))

            # Plot Error bar data recording intervals
            err = pg.ErrorBarItem(x=np.array(rec_midpoints), y=np.array(sta_ids), left=np.array(diff_frm_mid_list),
                                  right=np.array(diff_frm_mid_list), beam=0.06)

            self.plot.addItem(err)


class MainWindow(QtGui.QMainWindow, Ui_MainWindow):
    """
    Main Window for QC_Events_ASDF application
    """

    def __init__(self):
        super(MainWindow, self).__init__()
        Ui_MainWindow.__init__(self)
        self.setupUi(self)

        self.open_db_button.released.connect(self.open_db_file)
        self.open_ASDF_button.released.connect(self.open_asdf_file)
        self.open_cat_button.released.connect(self.open_cat_file)

        self.action_upd_xml_sql.triggered.connect(self.upd_xml_sql)
        self.action_get_gaps_sql.triggered.connect(self.get_gaps_sql)
        self.action_plot_gaps_overlaps.triggered.connect(self.plot_gaps_overlaps)

        self.station_view.itemClicked.connect(self.station_view_itemClicked)

        # set up dictionary for differnet ASDF files and associated attributes
        self.ASDF_accessor = {}

        cache = QtNetwork.QNetworkDiskCache()
        cache.setCacheDirectory("cache")
        self.web_view.page().networkAccessManager().setCache(cache)
        self.web_view.page().networkAccessManager()

        self.web_view.page().mainFrame().addToJavaScriptWindowObject("MainWindow", self)
        self.web_view.page().setLinkDelegationPolicy(QtWebKit.QWebPage.DelegateAllLinks)
        self.web_view.load(QtCore.QUrl('map.html'))
        self.web_view.loadFinished.connect(self.onLoadFinished)
        self.web_view.linkClicked.connect(QtGui.QDesktopServices.openUrl)

        self.show()
        self.raise_()

    def onLoadFinished(self):
        with open('map.js', 'r') as f:
            frame = self.web_view.page().mainFrame()
            frame.evaluateJavaScript(f.read())

    @QtCore.pyqtSlot(float, float, str, str, int)
    def onMap_marker_selected(self, lat, lng, event_id, df_id, row_index):
        self.selected_file = os.path.basename(self.root_asdf_filename)
        self.station_view_itemClicked(self.ASDF_accessor[self.selected_file]['file_tree_item'])
        self.table_view_highlight(self.tbl_view_dict[str(df_id)], row_index)

    @QtCore.pyqtSlot(int)
    def onMap_stn_marker_selected(self, station):
        self.station_view.setCurrentItem(self.station_view.topLevelItem(0))

    def changed_widget_focus(self):
        try:
            if not QtGui.QApplication.focusWidget() == self.graph_view:
                self.scatter_point_deselect()
        except AttributeError:
            pass

    def open_asdf_file(self):
        self.root_asdf_filename = str(QtGui.QFileDialog.getOpenFileName(
            parent=self, caption="Choose ASDF File",
            directory=os.path.expanduser("~"),
            filter="ASDF Files (*.h5)"))
        if not self.root_asdf_filename:
            return

        # open up the asdf file containing all of the waveforms for a network
        waveform_ds = pyasdf.ASDFDataSet(self.root_asdf_filename)
        basename_file = os.path.basename(self.root_asdf_filename)

        # add it to the ASDF accessor
        self.ASDF_accessor[basename_file] = {"ds": waveform_ds, "is_root": True}

        self.build_station_view_list(basename_file)
        # self.plot_stations()

    def open_db_file(self):

        self.web_view.page().mainFrame().evaluateJavaScript("removeStnMarkers();")


        self.db_filename = str(QtGui.QFileDialog.getOpenFileName(
            parent=self, caption="Choose JSON Database File",
            directory=os.path.expanduser(os.path.dirname(self.root_asdf_filename)),
            filter="JSON Database File (*.json)"))
        if not self.db_filename:
            return

        print('')
        print("Initializing Database..")

        # create the seismic database
        self.seisdb = SeisDB(json_file=self.db_filename)

        print("Seismic Database Initilized!")

    def open_cat_file(self):
        self.cat_filename = str(QtGui.QFileDialog.getOpenFileName(
            parent=self, caption="Choose Earthquake Catalogue QuakeML File",
            directory=os.path.expanduser("~"),
            filter="XML Files (*.xml)"))
        if not self.cat_filename:
            return

        cat = read_events(self.cat_filename)

        # create empty data frame
        cat_df = pd.DataFrame(data=None, columns=['event_id', 'qtime', 'lat', 'lon', 'depth', 'mag'])

        # iterate through the events
        for _i, event in enumerate(cat):
            # Get quake origin info
            origin_info = event.preferred_origin() or event.origins[0]

            try:
                mag_info = event.preferred_magnitude() or event.magnitudes[0]
                magnitude = mag_info.mag
            except IndexError:
                # No magnitude for event
                magnitude = None

            cat_df.loc[_i] = [str(event.resource_id.id).split('=')[1], int(origin_info.time.timestamp),
                                   origin_info.latitude, origin_info.longitude,
                                   origin_info.depth / 1000, magnitude]

        cat_df.reset_index(drop=True, inplace=True)

        print('------------')
        print(cat_df)

        self.ASDF_accessor[self.selected_file]['cat'] = cat
        self.ASDF_accessor[self.selected_file]['cat_df'] = cat_df

        self.build_tables()
        self.plot_events()

    def plot_stations(self):
        ds = self.ASDF_accessor[self.selected_file]['ds']
        if 'ref_stns' in self.ASDF_accessor[self.selected_file].keys():
            ref_stations = self.ASDF_accessor[self.selected_file]['ref_stns']
        else:
            ref_stations = []

        # save all of the coords for later
        temp_x_coords = []
        temp_y_coords = []
        # iterate through the stations with the coords
        for station_id, coordinates in ds.get_all_coordinates().items():
            if not coordinates:
                continue

            latitude = coordinates["latitude"]
            longitude = coordinates["longitude"]

            # append the lats and lons to temp lists
            temp_x_coords.append(longitude)
            temp_y_coords.append(latitude)

            if not station_id in ref_stations:
                js_call = "addStation('{station_id}', {latitude}, {longitude});" \
                    .format(station_id=station_id, latitude=latitude,
                            longitude=longitude)
                self.web_view.page().mainFrame().evaluateJavaScript(js_call)
            else:
                # plot the reference stations
                js_call = "addRefStation('{station_id}', {latitude}, {longitude});" \
                    .format(station_id=station_id, latitude=latitude,
                            longitude=longitude)
                self.web_view.page().mainFrame().evaluateJavaScript(js_call)

        self.ASDF_accessor[self.selected_file]['station_coords'] = (temp_x_coords, temp_y_coords)

    def plot_events(self):
        cat_df = self.ASDF_accessor[self.selected_file]['cat_df']
        # Plot the events
        for row_index, row in cat_df.iterrows():
            js_call = "addEvent('{event_id}', '{df_id}', {row_index}, " \
                      "{latitude}, {longitude}, '{a_color}', '{p_color}');" \
                .format(event_id=row['event_id'], df_id="cat", row_index=int(row_index), latitude=row['lat'],
                        longitude=row['lon'], a_color="Red",
                        p_color="#008000")
            self.web_view.page().mainFrame().evaluateJavaScript(js_call)

    def build_station_view_list(self, ds_id):
        # self.station_view.clear()

        ds = self.ASDF_accessor[ds_id]['ds']

        items = []

        # persistent list for all stations within ASDF file
        sta_list = []
        #set with unique channel codes in survey
        channel_codes_set = set()

        filename_item = QtGui.QTreeWidgetItem([ds_id],
                                              type=STATION_VIEW_ITEM_TYPES["FILE"])

        # add the tree item for the ASDF file into accessor dict
        self.ASDF_accessor[ds_id]['file_tree_item'] = filename_item

        self.station_view_itemClicked(filename_item)


        # Iterate through station accessors in ASDF file
        for key, group in itertools.groupby(
                ds.waveforms,
                key=lambda x: x._station_name.split(".")[0]):
            network_item = QtGui.QTreeWidgetItem(
                [key],
                type=STATION_VIEW_ITEM_TYPES["NETWORK"])
            group = sorted(group, key=lambda x: x._station_name)
            # Add all children stations.
            for station in sorted(group, key=lambda x: x._station_name):
                station_item = QtGui.QTreeWidgetItem([
                    station._station_name.split(".")[-1]],
                    type=STATION_VIEW_ITEM_TYPES["STATION"])

                sta_list.append(station._station_name)

                # get stationxml (to channel level) for station
                station_inv = station.StationXML[0][0]
                print(station_inv)

                # add info children
                station_children = [
                    QtGui.QTreeWidgetItem(['StartDate: \t%s' % station_inv.start_date.strftime('%Y-%m-%dT%H:%M:%S')],
                                          type=STATION_VIEW_ITEM_TYPES["STN_INFO"]),
                    QtGui.QTreeWidgetItem(['EndDate: \t%s' % station_inv.end_date.strftime('%Y-%m-%dT%H:%M:%S')],
                                          type=STATION_VIEW_ITEM_TYPES["STN_INFO"]),
                    QtGui.QTreeWidgetItem(['Latitude: \t%s' % station_inv.latitude], type=STATION_VIEW_ITEM_TYPES["STN_INFO"]),
                    QtGui.QTreeWidgetItem(['Longitude: \t%s' % station_inv.longitude],
                                          type=STATION_VIEW_ITEM_TYPES["STN_INFO"]),
                    QtGui.QTreeWidgetItem(['Elevation: \t%s' % station_inv.elevation],
                                          type=STATION_VIEW_ITEM_TYPES["STN_INFO"])]

                station_item.addChildren(station_children)

                # add channel items
                for channel_inv in station_inv:
                    #add the channel code to list
                    channel_codes_set.add(channel_inv.code)

                    channel_item = QtGui.QTreeWidgetItem(
                        [channel_inv.code], type=STATION_VIEW_ITEM_TYPES["CHANNEL"])

                    channel_children = [
                        QtGui.QTreeWidgetItem(['StartDate: \t%s' % station_inv.start_date.strftime('%Y-%m-%dT%H:%M:%S')],
                                              type=STATION_VIEW_ITEM_TYPES["CHAN_INFO"]),
                        QtGui.QTreeWidgetItem(['EndDate: \t%s' % station_inv.end_date.strftime('%Y-%m-%dT%H:%M:%S')],
                                              type=STATION_VIEW_ITEM_TYPES["CHAN_INFO"]),
                        QtGui.QTreeWidgetItem(['Location: \t%s' % channel_inv.location_code],
                                              type=STATION_VIEW_ITEM_TYPES["CHAN_INFO"]),
                        QtGui.QTreeWidgetItem(['SamplRate: \t%s' % channel_inv.sample_rate],
                                              type=STATION_VIEW_ITEM_TYPES["CHAN_INFO"]),
                        QtGui.QTreeWidgetItem(['Azimuth: \t%s' % channel_inv.azimuth],
                                              type=STATION_VIEW_ITEM_TYPES["CHAN_INFO"]),
                        QtGui.QTreeWidgetItem(['Dip: \t%s' % channel_inv.dip], type=STATION_VIEW_ITEM_TYPES["CHAN_INFO"]),
                        QtGui.QTreeWidgetItem(['Latitude: \t%s' % channel_inv.latitude],
                                              type=STATION_VIEW_ITEM_TYPES["CHAN_INFO"]),
                        QtGui.QTreeWidgetItem(['Longitude: \t%s' % channel_inv.longitude],
                                              type=STATION_VIEW_ITEM_TYPES["CHAN_INFO"]),
                        QtGui.QTreeWidgetItem(['Elevation: \t%s' % channel_inv.elevation],
                                              type=STATION_VIEW_ITEM_TYPES["CHAN_INFO"])]

                    channel_item.addChildren(channel_children)

                    station_item.addChild(channel_item)

                network_item.addChild(station_item)
            filename_item.addChild(network_item)
        items.append(filename_item)

        self.station_view.insertTopLevelItems(0, items)

        # make the channel code set into list and make persistant
        self.ASDF_accessor[ds_id]['channel_codes'] = list(channel_codes_set)
        self.ASDF_accessor[ds_id]['sta_list'] = sta_list

    def station_view_itemClicked(self, item):
        t = item.type()

        def get_station(item):
            station = item.text(0)
            if "." not in station:
                station = item.parent().text(0) + "." + station
            return station

        if t == STATION_VIEW_ITEM_TYPES["FILE"]:
            self.selected_file = str(item.text(0))
            # set currently selected asdf file to blue and set all others to green
            for value in self.ASDF_accessor.values():
                value['file_tree_item'].setBackgroundColor(0, QtGui.QColor('green'))
            self.ASDF_accessor[self.selected_file]['file_tree_item'].setBackgroundColor(0, QtGui.QColor('blue'))

            self.plot_stations()
            if 'cat_df' in self.ASDF_accessor.keys():
                self.plot_events()
                self.build_tables()

        elif t == STATION_VIEW_ITEM_TYPES["NETWORK"]:
            pass
        elif t == STATION_VIEW_ITEM_TYPES["STATION"]:
            station = get_station(item)

            # Highlight the station marker on the map
            js_call = "highlightStation('{station}');".format(station=station.split('.')[1])
            self.web_view.page().mainFrame().evaluateJavaScript(js_call)
        else:
            pass

    def tbl_view_popup(self):

        cat_df = self.ASDF_accessor[self.selected_file]['cat_df']

        focus_widget = QtGui.QApplication.focusWidget()
        # get the selected row number
        row_number = focus_widget.selectionModel().selectedRows()[0].row()
        row_index = self.table_accessor[focus_widget][1][row_number]

        self.selected_row = cat_df.loc[row_index]

        self.rc_menu = QtGui.QMenu(self)
        self.rc_menu.addAction('Open Earthquake with SG2K', functools.partial(
            self.create_SG2K_initiate, self.selected_row['event_id'], self.selected_row, row_index))

        self.rc_menu.popup(QtGui.QCursor.pos())

    def build_tables(self):
        cat_df = self.ASDF_accessor[self.selected_file]['cat_df']

        self.table_accessor = None

        dropped_cat_df = cat_df

        # make UTC string from earthquake cat and add julian day column
        def mk_cat_UTC_str(row):
            return (pd.Series([UTCDateTime(row['qtime']).ctime(), UTCDateTime(row['qtime']).julday]))

        dropped_cat_df[['Q_time_str', 'julday']] = dropped_cat_df.apply(mk_cat_UTC_str, axis=1)

        self.tbld = TableDialog(parent=self, cat_df=dropped_cat_df)


        if self.ASDF_accessor[self.selected_file]['is_root']:
            self.tbld.cat_event_table_view.setContextMenuPolicy(QtCore.Qt.CustomContextMenu)
            self.tbld.cat_event_table_view.customContextMenuRequested.connect(self.tbl_view_popup)


        # Lookup Dictionary for table views
        self.tbl_view_dict = {"cat": self.tbld.cat_event_table_view}

        # Create a new table_accessor dictionary for this class
        self.table_accessor = {self.tbld.cat_event_table_view: [dropped_cat_df, range(0, len(dropped_cat_df))]}

        self.tbld.cat_event_table_view.clicked.connect(self.table_view_clicked)

        # If headers are clicked then sort
        self.tbld.cat_event_table_view.horizontalHeader().sectionClicked.connect(self.headerClicked)

    def headerClicked(self, logicalIndex):
        focus_widget = QtGui.QApplication.focusWidget()
        table_df = self.table_accessor[focus_widget][0]

        header = focus_widget.horizontalHeader()

        self.order = header.sortIndicatorOrder()
        table_df.sort_values(by=table_df.columns[logicalIndex],
                             ascending=self.order, inplace=True)

        self.table_accessor[focus_widget][1] = table_df.index.tolist()

        if focus_widget == self.tbld.cat_event_table_view:
            self.model = PandasModel(table_df, cat_nm=True)

        focus_widget.setModel(self.model)
        focus_widget.update()

    def table_view_clicked(self):
        self.selected_file = os.path.basename(self.root_asdf_filename)
        self.station_view_itemClicked(self.ASDF_accessor[self.selected_file]['file_tree_item'])

        focus_widget = QtGui.QApplication.focusWidget()
        row_number = focus_widget.selectionModel().selectedRows()[0].row()
        row_index = self.table_accessor[focus_widget][1][row_number]
        # Highlight/Select the current row in the table
        self.table_view_highlight(focus_widget, row_index)

    def table_view_highlight(self, focus_widget, row_index):

        cat_df = self.ASDF_accessor[self.selected_file]['cat_df']

        if focus_widget == self.tbld.cat_event_table_view:
            self.selected_row = cat_df.loc[row_index]

            # Find the row_number of this index
            cat_row_number = self.table_accessor[focus_widget][1].index(row_index)
            focus_widget.selectRow(cat_row_number)

            # Highlight the marker on the map
            js_call = "highlightEvent('{event_id}');".format(event_id=self.selected_row['event_id'])
            self.web_view.page().mainFrame().evaluateJavaScript(js_call)

    def create_SG2K_initiate(self, event, quake_df, cat_id):

        ds = self.ASDF_accessor[self.selected_file]['ds']

        cat = self.ASDF_accessor[self.selected_file]['cat']
        cat_single = cat[cat_id]

        sta_list = self.ASDF_accessor[self.selected_file]['sta_list']
        chan_list = self.ASDF_accessor[self.selected_file]['channel_codes']
        station_coords = self.ASDF_accessor[self.selected_file]['station_coords']

        # Launch the custom station/component selection dialog
        sel_dlg = selectionDialog(parent=self, sta_list=sta_list, chan_list=chan_list)
        if sel_dlg.exec_():
            select_net, select_sta, select_comp = sel_dlg.getSelected()
            # print(select_sta)
            # print(select_comp)

            path_asdf = os.path.join(os.path.dirname(self.cat_filename), event)
            # specify output ASDF
            temp_ASDF_out = os.path.join(path_asdf, event + '.h5')

            # create directory
            if os.path.exists(path_asdf):
                shutil.rmtree(path_asdf, ignore_errors=True)

            try:
                os.mkdir(path_asdf)
            except:
                pass

            # open up the ASDF file
            query_ds = pyasdf.ASDFDataSet(temp_ASDF_out)

            # earthquake time for json query
            quake_time = UTCDateTime(quake_df['qtime']).timestamp

            # query for data 5 minutes before earthquake and 15 minutes after
            qu_starttime = quake_time - (5 * 60)
            qu_endtime = quake_time + (15 * 60)

            # Create a Stream object to put data into
            # st = Stream()
            # Create a dictionary to put traces into (keys are tr_ids)
            st_dict = defaultdict(list)
            inv_dict = {}

            print('---------------------------------------')
            print('Finding Data for Earthquake: ' + event)


            select_tags = ["raw_recording"]



            print(select_net, select_sta, select_comp, select_tags, qu_starttime, qu_endtime)
            query = self.seisdb.queryByTime(select_net, select_sta, select_comp, select_tags, qu_starttime, qu_endtime)
            for matched_info in query.values():
                print(matched_info["ASDF_tag"])

                # get the station accessor from the ASDF file
                sta_accessor  = ds.waveforms[matched_info["new_network"] + '.' + matched_info["new_station"]]

                # get the stationxml data
                inv = sta_accessor.StationXML

                # read the data from the root ASDF into stream
                temp_tr = sta_accessor[matched_info["ASDF_tag"]][0]

                print(temp_tr)
                temp_tr.plot()


                # trim trace to start and endtime
                temp_tr.trim(starttime=UTCDateTime(qu_starttime), endtime=UTCDateTime(qu_endtime))

                # append trace into dictionary
                st_dict[temp_tr.get_id()].append(temp_tr)

                # add the associated inv into another dict
                inv_dict[matched_info["new_network"] + '.' + matched_info["new_station"]] = inv

            waveforms_added = False

            # free memory
            temp_st = None
            temp_tr = None

            if not len(st_dict) == 0:
                # .__nonzero__():

                print('')
                print('Merging Traces from %s Stations....' % len(st_dict))
                # Attempt to merge all traces with matching ID'S (same keys in dict) in place
                # st.merge()

                for key in st_dict.keys():
                    merged_st = Stream()
                    for temp_tr in st_dict[key]:
                        merged_st.append(temp_tr)
                        temp_tr = None
                    merged_st.merge()

                    st_dict[key] = merged_st[0]


                    print("Station {0} has {1} Seconds of data".format(key, merged_st[0].stats.endtime - merged_st[0].stats.starttime))

                    merged_st = None


                print('\nTrimming Traces to 20 mins around earthquake time....')

                # now trim the st object to 5 mins
                # before query time and 15 minutes afterwards


                for key in st_dict.keys():

                    st_dict[key] = st_dict[key].trim(starttime=UTCDateTime(qu_starttime),
                                                     endtime=UTCDateTime(qu_endtime), pad=True, fill_value=0)





                # write traces into ASDF
                query_ds.add_quakeml(cat_single)
                for key in inv_dict.keys():
                    query_ds.add_stationxml(inv_dict[key])
                for key in st_dict.keys():
                    waveforms_added = True
                    query_ds.add_waveforms(st_dict[key], tag="extracted_event", event_id=cat_single)
                    st_dict[key].write(os.path.join(path_asdf, st_dict[key].get_id() + ".MSEED"), format="MSEED")
                    # if type(st_dict[key]) == Stream:
                    #     #there is a problem with network codes (two stations named the same)
                    #     #ignore it for now
                    #     continue
                    # # st_dict[key].write(os.path.join(temp_seed_out, st_dict[key].get_id() + ".MSEED"), format="MSEED")


                print("\nAdded Wavefomrs associated with event to ASDF file: " + temp_ASDF_out)
                print('')
            else:
                print("No Data for Earthquake!")

            # free memory
            st_dict = None

            ref_stations = []
            # Now requesting reference station data from IRIS if desired
            if self.ref_radioButton.isChecked():

                ref_dir = os.path.join(path_asdf, 'ref_data')

                # create ref directory
                if os.path.exists(ref_dir):
                    shutil.rmtree(ref_dir)
                os.mkdir(ref_dir)

                # request stations that are close to the selected stations

                # first use the coords lists to get a bounding box for array
                def calc_bounding_box(x, y):
                    min_x, max_x = (min(x), max(x))
                    min_y, max_y = (min(y), max(y))

                    return (min_x, max_x, min_y, max_y)

                bb = calc_bounding_box(station_coords[0], station_coords[1])

                # request data for near earthquake time up to 5 degrees from bounding box of array
                print('\nRequesting Waveform Data from Nearby Permanent Network Stations....')

                client = Client("IRIS")
                ref_inv = client.get_stations(network="AU",
                                                   starttime=UTCDateTime(quake_df['qtime'] - (5 * 60)),
                                                   endtime=UTCDateTime(quake_df['qtime'] + (15 * 60)),
                                                   minlongitude=bb[0]-2,
                                                   maxlongitude=bb[1]+2,
                                                   minlatitude=bb[2]-2,
                                                   maxlatitude=bb[3]+2,
                                                   level='channel')

                print(ref_inv)

                ref_st = Stream()
                inv = []

                # go through inventory and request timeseries data
                for net in ref_inv:
                    for stn in net:
                        try:
                            ref_st += client.get_waveforms(network=net.code, station=stn.code, channel='*', location='*',
                                                       starttime=UTCDateTime(quake_df['qtime'] - (5 * 60)),
                                                       endtime=UTCDateTime(quake_df['qtime'] + (15 * 60)))
                        except FDSNException:
                            print('No Data for Earthquake from Reference Station: ' + stn.code)

                        else:
                            # # plot the reference stations
                            # js_call = "addRefStation('{station_id}', {latitude}, {longitude});" \
                            #     .format(station_id=stn.code, latitude=stn.latitude,
                            #             longitude=stn.longitude)
                            # self.web_view.page().mainFrame().evaluateJavaScript(js_call)

                            ref_stations.append(net.code + '.' + stn.code)
                            # append the inv
                            inv.append(ref_inv.select(station=stn.code))


                # write ref traces into ASDF
                for st_inv in inv:
                    query_ds.add_stationxml(st_inv)
                for tr in ref_st:
                    waveforms_added = True
                    query_ds.add_waveforms(tr, "reference_station", event_id=cat_single)
                    tr.write(os.path.join(ref_dir, tr.id + ".MSEED"), format="MSEED")
                print("Wrote Reference Waveforms to ASDF file: " + temp_ASDF_out)
                print('\nEarthquake Data Query Done!!!')

                ref_inv.write(os.path.join(ref_dir, "ref_metadata.xml"), format="STATIONXML")

            if waveforms_added:
                # now add the asdf file into view
                self.ASDF_accessor[os.path.basename(temp_ASDF_out)] = {"ds": query_ds, "ref_stns": ref_stations}

                self.build_station_view_list(os.path.basename(temp_ASDF_out))

            else:
                del query_ds

    def upd_xml_sql(self):
        # Look at the SQL database and create dictionary for start and end dates for each station
        # iterate through stations

        print("\nQuerying SQLite database for start/end dates for each station")
        print("This may take a while.......")

        def overwrite_info(st, et):
            # fix the station inventory
            self.inv[0][i].start_date = st
            self.inv[0][i].end_date = et

            # Fix the channel
            for _j, chan in enumerate(self.inv[0][i]):
                self.inv[0][i][_j].start_date = st
                self.inv[0][i][_j].end_date = et

        for i, station_obj in enumerate(self.inv[0]):
            station = station_obj.code
            comp_regex = re.compile('..Z')

            if os.path.splitext(self.db_filename)[1] == ".db":

                for min_max in self.session.query(func.min(Waveforms.starttime), func.max(Waveforms.endtime)). \
                        filter(Waveforms.station == station, Waveforms.component.like('__Z')):
                    start_time = UTCDateTime(min_max[0])
                    end_time = UTCDateTime(min_max[1])

            elif os.path.splitext(self.db_filename)[1] == ".json":
                temp_extent = []
                for key, matched_entry in self.network_dict.iteritems():
                    if (matched_entry['station'] == station) and re.match(comp_regex, matched_entry['component']):
                        if len(temp_extent) == 0:
                            # first iteration
                            temp_extent = [matched_entry['starttime'], matched_entry['endtime']]
                            continue

                        # check the current iterate
                        if (matched_entry['starttime'] < temp_extent[0]):
                            temp_extent[0] = matched_entry['starttime']

                        if (matched_entry['endtime'] > temp_extent[1]):
                            temp_extent[1] = matched_entry['endtime']

                start_time = UTCDateTime(temp_extent[0])
                end_time = UTCDateTime(temp_extent[1])

            print("\nRecording interval for: " + station)
            print("\tStart Date: " + start_time.ctime())
            print("\tEnd Date:   " + end_time.ctime())

            overwrite_info(start_time, end_time)

        # Overwrite the original station XML file
        self.inv.write(self.stn_filename, format="STATIONXML")
        print("\nFinished Updating StationXML file: " + self.stn_filename)

    def get_gaps_sql(self):
        # go through SQL entries and find all gaps save them into dictionary
        self.recording_gaps = {}
        self.recording_overlaps = {}
        self.recording_intervals = {}

        print('_________________')

        print("\nIterating through SQL entries to find data gaps")
        print("This may take a while......")

        # iterate through stations
        for _i, station in enumerate(self.station_list):
            print "\r Working on Station: " + station + ", " + str(_i + 1) + " of " + \
                  str(len(self.station_list)) + " Stations",
            sys.stdout.flush()
            self.recording_gaps[station] = {}
            self.recording_overlaps[station] = {}
            self.recording_intervals[station] = {}

            # store for previous end time for a particular component in dictionary
            comp_endtime_dict = {}
            gaps_no_dict = {}
            ovlps_no_dict = {}

            # create new entry into recording gaps dict for each channel
            for chan in self.channel_codes:
                self.recording_gaps[station][chan] = []
                self.recording_overlaps[station][chan] = []
                self.recording_intervals[station][chan] = []
                gaps_no_dict[chan] = 0
                ovlps_no_dict[chan] = 0

            if os.path.splitext(self.db_filename)[1] == ".db":
                for entry in (self.session.query(Waveforms)
                                      .filter(Waveforms.station == station)
                                      .order_by(Waveforms.starttime)):

                    # print(entry.ASDF_tag)
                    # print(UTCDateTime(entry.starttime).ctime())
                    # print(UTCDateTime(entry.endtime).ctime())
                    # print(entry.waveform_basename)
                    # print(entry.path)

                    # if there is a previous timestamp in the dict then calculate diff tween the previous endtime and the
                    # currently iterated starttime
                    if entry.component in comp_endtime_dict.keys():
                        """
                        This is where the algorithm to analyse gaps/overlaps would go
                        for now it is just a simple analysis to find large data gaps (corresponding to service intervals)
                        """

                        prev_endtime = comp_endtime_dict[entry.component]

                        diff = entry.starttime - prev_endtime

                        # get large gap
                        if diff > 1:
                            gaps_no_dict[entry.component] += 1
                            self.recording_gaps[station][entry.component].append({"gap_start": prev_endtime,
                                                                                  "gap_end": entry.starttime})
                            # print(UTCDateTime(prev_endtime).ctime(), UTCDateTime(entry.starttime).ctime())
                        # check if overalp
                        elif diff < -1:
                            ovlps_no_dict[entry.component] += 1
                            self.recording_overlaps[station][entry.component].append({"ovlp_start": entry.starttime,
                                                                                      "ovlp_end": prev_endtime})

                        # add current iterate to dictionary
                        comp_endtime_dict[entry.component] = entry.endtime

                    else:
                        # there is no component in dictionary (i.e first iteration for component)
                        # add current iterate to dictionary
                        comp_endtime_dict[entry.component] = entry.endtime

            elif os.path.splitext(self.db_filename)[1] == ".json":
                # sort the dictionary by the starttime field
                sorted_keys = sorted(self.network_dict, key=lambda x: self.network_dict[x]['starttime'])

                for key in sorted_keys:
                    entry = self.network_dict[key]
                    if (entry['station'] == station):

                        # print(entry['ASDF_tag'])
                        # print(UTCDateTime(entry['starttime']).ctime())
                        # print(UTCDateTime(entry['endtime']).ctime())
                        # print(key)
                        # print(entry['path'])

                        # if there is a previous timestamp in the dict then calculate diff tween the previous endtime and the
                        # currently iterated starttime
                        if entry['component'] in comp_endtime_dict.keys():
                            """
                            This is where the algorithm to analyse gaps/overlaps would go
                            for now it is just a simple analysis to find large data gaps (corresponding to service intervals)
                            """

                            prev_endtime = comp_endtime_dict[entry['component']]

                            diff = entry['starttime'] - prev_endtime

                            # get large gap
                            if diff > 1:
                                gaps_no_dict[entry['component']] += 1
                                self.recording_gaps[station][entry['component']].append({"gap_start": prev_endtime,
                                                                                         "gap_end": entry['starttime']})
                                # print(UTCDateTime(prev_endtime).ctime(), UTCDateTime(entry['starttime).ctime())
                            # check if overalp
                            elif diff < -1:
                                ovlps_no_dict[entry['component']] += 1
                                self.recording_overlaps[station][entry['component']].append(
                                    {"ovlp_start": entry['starttime'],
                                     "ovlp_end": prev_endtime})

                            # add current iterate to dictionary
                            comp_endtime_dict[entry['component']] = entry['endtime']

                        else:
                            # there is no component in dictionary (i.e first iteration for component)
                            # add current iterate to dictionary
                            comp_endtime_dict[entry['component']] = entry['endtime']

                            # # print("Found: ")
                            # for chan in self.channel_codes:
                            #     print("\tChannel: " + chan +" "+ str(gaps_no_dict[chan]) +
                            #           " Gaps and " + str(ovlps_no_dict[chan]) + " Overlaps!")

        self.calculate_recording_int()

    def calculate_recording_int(self):
        # iterate through stations
        for i, station_obj in enumerate(self.inv[0]):
            station = station_obj.code

            # get the start_date and end_date for station recording
            rec_start = self.inv[0][i].start_date.timestamp
            rec_end = self.inv[0][i].end_date.timestamp

            # store for previous end time for a particular component in dictionary
            comp_endtime_dict = {}

            # iterate through channels
            for chan_key, gaps_list in self.recording_gaps[station].iteritems():
                # iterate through gaps list
                gaps_no = len(gaps_list)
                for _j, gap_entry in enumerate(gaps_list):
                    if _j == 0:
                        # first interval
                        # print(UTCDateTime(rec_start).ctime(), UTCDateTime(gap_entry['gap_start']).ctime())
                        self.recording_intervals[station][chan_key].append({'rec_start': rec_start,
                                                                            'rec_end': gap_entry['gap_start']})

                    elif _j == gaps_no - 1:
                        # last interval
                        # print(UTCDateTime(gap_entry['gap_end']).ctime(), UTCDateTime(rec_end).ctime())
                        self.recording_intervals[station][chan_key].append({'rec_start': gap_entry['gap_end'],
                                                                            'rec_end': rec_end})

                    else:
                        if chan_key in comp_endtime_dict.keys():
                            prev_endtime = comp_endtime_dict[chan_key]
                            # print(UTCDateTime(gaps_list[_j-1]['gap_end']).ctime(), UTCDateTime(gap_entry['gap_start']).ctime())
                            self.recording_intervals[station][chan_key].append({'rec_start': prev_endtime,
                                                                                'rec_end': gap_entry['gap_start']})
                    comp_endtime_dict[chan_key] = gap_entry['gap_end']

        print("")
        print("\nFinished calculating station recording intervals")
        print("Produced output: ")

    def plot_gaps_overlaps(self):
        self.data_avail_plot = DataAvailPlot(parent=self, sta_list=self.station_list,
                                             chan_list=self.channel_codes,
                                             rec_int_dict=self.recording_intervals)


if __name__ == '__main__':
    proxy_queary = query_yes_no("Input Proxy Settings?")

    if proxy_queary == 'yes':
        print('')
        proxy = raw_input("Proxy:")
        port = raw_input("Proxy Port:")
        try:
            networkProxy = QtNetwork.QNetworkProxy(QtNetwork.QNetworkProxy.HttpProxy, proxy, int(port))
            QtNetwork.QNetworkProxy.setApplicationProxy(networkProxy)
        except ValueError:
            print('No proxy settings supplied..')
            sys.exit()

    app = QtGui.QApplication([])
    w = MainWindow()
    w.raise_()
    app.exec_()
