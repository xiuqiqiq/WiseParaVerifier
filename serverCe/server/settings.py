 #coding=utf-8

HOST = ''
# PORT = 50003
# PORT = 50008 # for calcutelate godsont reachable
PORT = 50009
# PORT = 50004 
# PORT = 30008 

# maximum sleep time while there is no connect for a smv process
MAX_SLEEP_TIME = 5

# time out in seconds
TIME_OUT = 5
MU_CHECK_TIMEOUT = 600
MU_CHECK_MEMORY = 1024

# path to NuSMV
SMV_PATH = '/home/lyj238/NuSMV-2.6.0-Linux/bin/NuSMV'
#SMV_PATH = '/home/lyj238/nusmv/NuSMV-2.5.4-x86_64-unknown-linux-gnu/bin/NuSMV'
MU_PATH = '/home/lyj238/ctf/murphi_r_2/src/mu'
MU_INCLUDE = '/home/lyj238/ctf/murphi_r_2/include'
GXX_PATH = '/usr/bin/g++'

# path for storing smv files
SMV_FILE_DIR = '/tmp/NuSMV2/'
MU_FILE_DIR = '/tmp/cmurphi2/'



dirs = [SMV_FILE_DIR, MU_FILE_DIR]

import os

for d in dirs:
    if not os.path.isdir(d):
        os.makedirs(d)
