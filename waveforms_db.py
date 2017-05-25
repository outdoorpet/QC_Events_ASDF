from sqlalchemy import Column, Integer, String
from sqlalchemy.ext.declarative import declarative_base

# Set up the sql waveform databases
Base = declarative_base()


class Waveforms(Base):
    __tablename__ = 'waveforms'
    # Here we define columns for the table
    starttime = Column(Integer)
    endtime = Column(Integer)
    orig_network = Column(String(2), nullable=False)
    new_network = Column(String(2), nullable=False)
    station = Column(String(5), nullable=False)
    component = Column(String(3), nullable=False)
    location = Column(String(2), nullable=False)
    waveform_basename = Column(String(40), nullable=False, primary_key=True)
    path = Column(String(100), nullable=False)
    ASDF_tag = Column(String(100), nullable=False)