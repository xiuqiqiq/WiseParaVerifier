#coding=utf-8

import time
import socket

HOST = '192.168.1.34'
PORT = 50008

file_path = "server/smvserv/mutualEx.smv"

content = ""
with open(file_path, "r") as file:
    content = file.read()


s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
s.connect((HOST, PORT))
# to_check = f'1,1,mutualEx,{content}'
to_check_2 = '2,1,mutualEx,(n[1] = c -> n[2] != c)'
quit = '7,1,n_g2k'
check_length  = len(to_check_2)
# data_to_send = f"{check_length},{to_check}"
data_to_send_2 = f"{check_length},{to_check_2}"
# s.send(data_to_send.encode())
# data = s.recv(1024)
# print(data)
s.send(data_to_send_2.encode())
data_2 = s.recv(1024)
print(data_2)

s.close()
