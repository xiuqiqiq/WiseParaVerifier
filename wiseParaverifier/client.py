import socket
from murphiparser import *
import threading
import time

class EmptyException(Exception):
    pass

class ServerException(Exception):
    pass


class RequestType:
    ERROR = -2
    WAITING = -1
    OK = 0
    COMPUTE_REACHABLE = 1
    QUERY_REACHABLE = 2
    CHECK_INV = 3
    SMV_QUIT = 7
    GO_BMC = 10
    CHECK_INV_BMC = 11
    SMV_BMC_QUIT = 12
    SET_SMT2_CONTEXT = 4
    QUERY_SMT2 = 5
    QUERY_STAND_SMT2 = 6
    SET_MU_CONTEXT = 8
    CHECK_INV_BY_MU = 9

def request_type_to_str(rt):
    if rt == RequestType.ERROR:
        return "-2"
    elif rt == RequestType.WAITING:
        return "-1"
    elif rt == RequestType.OK:
        return "0"
    elif rt == RequestType.COMPUTE_REACHABLE:
        return "1"
    elif rt == RequestType.QUERY_REACHABLE:
        return "2"
    elif rt == RequestType.CHECK_INV:
        return "3"
    elif rt == RequestType.SMV_QUIT:
        return "7"
    elif rt == RequestType.GO_BMC:
        return "10"
    elif rt == RequestType.CHECK_INV_BMC:
        return "11"
    elif rt == RequestType.SMV_BMC_QUIT:
        return "12"
    elif rt == RequestType.SET_SMT2_CONTEXT:
        return "4"
    elif rt == RequestType.QUERY_SMT2:
        return "5"
    elif rt == RequestType.QUERY_STAND_SMT2:
        return "6"
    elif rt == RequestType.SET_MU_CONTEXT:
        return "8"
    elif rt == RequestType.CHECK_INV_BY_MU:
        return "9"

def str_to_request_type(s):
    if s == "-2":
        return RequestType.ERROR
    elif s == "-1":
        return RequestType.WAITING
    elif s == "0":
        return RequestType.OK
    elif s == "1":
        return RequestType.COMPUTE_REACHABLE
    elif s == "2":
        return RequestType.QUERY_REACHABLE
    elif s == "3":
        return RequestType.CHECK_INV
    elif s == "7":
        return RequestType.SMV_QUIT
    elif s == "10":
        return RequestType.GO_BMC
    elif s == "11":
        return RequestType.CHECK_INV_BMC
    elif s == "12":
        return RequestType.SMV_BMC_QUIT
    elif s == "4":
        return RequestType.SET_SMT2_CONTEXT
    elif s == "5":
        return RequestType.QUERY_SMT2
    elif s == "6":
        return RequestType.QUERY_STAND_SMT2
    elif s == "8":
        return RequestType.SET_MU_CONTEXT
    elif s == "9":
        return RequestType.CHECK_INV_BY_MU
    else:
        raise Exception("error return code from server: " + s)


# 创建套接字并连接server、接收响应
def make_request(data, host, port):
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.connect((host, port))
    sock.send(data.encode())
    response = sock.recv(1024).decode()
    sock.close()
    return response


command_id = [0]

# 构建请求并处理响应消息
def request(cmd, req_str, host, port):
    cmd_str = request_type_to_str(cmd)
    cmd_id = command_id[0]
    req = f"{cmd_str},{cmd_id},{req_str}"
    wrapped = f"{len(req)},{req}"

    # 确保id的唯一性
    command_id[0] += 1

    response = make_request(wrapped, host, port)
    res = response.split(',')

    if not res:
        raise EmptyException()

    status = res[0]
    res_data = res[1:]

    s = str_to_request_type(status)
    if s == RequestType.ERROR:
        raise ServerException()
    else:
        return s, res_data

file_idx = 1
class Smv:
    class CannotCheck(Exception):
        pass

    host = '192.168.1.34'
    # port = 30008  
    # port = 50008    # godsont reachable
    port = 50009
    # port = 50004  #server_2

    @staticmethod
    def compute_reachable(name, content, smv_ord=""):
        status, _ = request(RequestType.COMPUTE_REACHABLE, f"{name},{content},{smv_ord}", Smv.host, Smv.port)
        return status == RequestType.OK

    @staticmethod
    def query_reachable(name):
        status, diameter = request(RequestType.QUERY_REACHABLE, name, Smv.host, Smv.port)
        if status == RequestType.OK:
            if diameter == ["-1"]:
                raise ServerException()
            else:
                try:
                    return int(diameter[0])
                except ValueError:
                    raise ServerException()
        else:
            return 0

    @staticmethod
    def check_inv(name, inv):
        status, res = request(RequestType.CHECK_INV, f"{name},{inv}", Smv.host, Smv.port)
        # global file_idx
        # protocol_content = ""
        # with open(f'protocols/flash/testFlash.smv') as file:
        #     protocol_content = file.read()
        # with open(f'smvbenchmark/flash_nodata_cub_Nxt/flash_nodata_cub_Nxt_{file_idx}.smv','w') as file:
        #     file.write(protocol_content)
        #     file.write("\n\n")
        #     file.write("INVAR\n")
        #     file.write(inv + ";")
        # file_idx = file_idx + 1

        if status == RequestType.OK:
            if res == ["0"]:
                raise Smv.CannotCheck()
            else:
                try:
                    return False if res[0].lower() == "false" else True
                except ValueError:
                    raise ServerException()
        else:
            raise ServerException()

    @staticmethod
    def quit(name):
        status, _ = request(RequestType.SMV_QUIT, name, Smv.host, Smv.port)
        return status == RequestType.OK

    
    @staticmethod
    def go_bmc(name, content):
        status, _ = request(RequestType.GO_BMC, f"{name},{content}", Smv.host, Smv.port)
        return status == RequestType.OK
    
    @staticmethod
    def check_inv_bmc(name, inv):
        status, res = request(RequestType.CHECK_INV_BMC, f"{name},{inv}", Smv.host, Smv.port)

        if status == RequestType.OK:
            if res == ["0"]:
                raise Smv.CannotCheck()
            else:
                try:
                    return False if res[0].lower() == "false" else True
                except ValueError:
                    raise ServerException()
        else:
            raise ServerException()




# table = {}

# 根据提供的协议，执行NuSMV计算可达集compute_reachable，并等待查询结果query_reachable
def set_context(name, smv_file_content, smv_ord=""):
    _res = Smv.compute_reachable(name, smv_file_content, smv_ord)
    diameter = 0
    while diameter == 0:
        import time
        time.sleep(1)
        diameter = Smv.query_reachable(name)
    return diameter


# def set_context(name, smv_file_content, smv_ord=""):
#     _res = Smv.compute_reachable(name, smv_file_content, smv_ord)




def set_bmc(name, smv_file_content):
    _res = Smv.go_bmc(name, smv_file_content)
    print("set bmc is:",_res)



def is_inv(name, inv=None, quiet=True):
    # if inv in table:
    #     return table[inv]
    # else:
    # global real_callSMV
    # real_callSMV = real_callSMV + 1
    if name == "":
        raise Exception("Protocol name not set")
    else:
        r = Smv.check_inv(name, inv)
        # table[inv] = r
        # print(inv,r)
        return r



def is_inv_bmc(name, inv=None):
    if name == "":
        raise Exception("Protocol name not set")
    else:
        r = Smv.check_inv_bmc(name, inv)
        return r


def calculate_protocol_reachability(name, smv_file_content, smv_ord=""):
    s_t = time.time()
    diameter = set_context(name, smv_file_content, smv_ord)
    e_t = time.time()
    print(f"calculate the reachability with: {e_t - s_t} s.")
    print(f"Protocol {name} has a reachability diameter of {diameter}")

# def calculate_protocol_reachability(name, smv_file_content, smv_ord=""):
#     set_context(name, smv_file_content, smv_ord)

# def check_invariants(name, invariants_list):
#     for inv in invariants_list:
#         is_true = is_inv(inv)
#         print(f"Invariant '{inv}' is {'true' if is_true else 'false'} for protocol {name}")

def check_invariants(name, invariant):
    is_true = is_inv(name, invariant)
    # print(f"Invariant '{invariant}' is {'true' if is_true else 'false'} for protocol {name}")
    return is_true


if __name__ == "__main__":

    # parse_name = "protocols/mutualEx/mutualEx"
    # parse_name = "protocols/heuristic_flash/flash"
    # parse_name = "protocols/mutdata/mutdata"
    # parse_name = "protocols/german_withoutData/german_withoutData"
    # parse_name = "protocols/german/german"
    # parse_name = "protocols/testpaxos/paxos_l"
    # parse_name = "protocols/heuristic_flash/flash"
    # parse_name = "protocols/flashNodata/flashNodata"
    # parse_name = "protocols/flash/flash_nodata"
    # parse_name = "protocols/flash_2/testFlash1"
    # parse_name = "protocols/flash/flashdebug"
    # parse_name = "protocols/two_phase_commit/two_phase_commit"
    # parse_name = "protocols/distributed_lock/distributed_lock"
    # parse_name = "protocols/distributed_lock/le_distributed_lock"
    # parse_name = "protocols/chord/chord"
    # parse_name = "protocols/M_mutualEx/mutualEx_M2"
    # parse_name = "protocols/client_server_db_ae/largerNODENUMS_client_server_db_ae"
    # parse_name = "protocols/consensus/consensusN3"
    # parse_name = "protocols/consensus_epr/largerQUORUMNUMS_consensus_epr"
    parse_name = "protocols/toy_consensus_fol/toy_consensus_fol"
    # parse_name = "protocols/consensus_epr/largerNODENUMS_consensus_epr"
    # parse_name = "protocols/godsont/godsont"
    # parse_name = "protocols/MESI/MESI"
    protocol_name = parse_name.split("/")[-1]
    # smv_content = str(parse_file(parse_name+".m", smvSelect = True))
    # with open(parse_name + ".smv", "w") as f:
    #     f.write(str(smv_content))
    smv_content = ""
    with open(parse_name + ".smv", "r") as file:
        smv_content = file.read()
    # calculate_protocol_reachability(protocol_name, smv_content)





    # print(check_invariants(protocol_name, "!(decided[2][2] & !member[1][1] & votes[1][2])")) 
    # print(check_invariants(protocol_name, "!(!t[1][2] & !request_sent[1][2] & db_request_sent[1][2] & !t[1][3])")) 
    # print(check_invariants(protocol_name, "!(!t[1][2] & !request_sent[1][2] & db_request_sent[1][2] & !request_sent[3][2])")) 




    

    set_bmc(protocol_name, smv_content)

    print(is_inv_bmc(protocol_name,"!(!voted[1] & decided[2] & !voted[2])"))

    


    


    

    

    

    

    
    
    
    
    
    




# /// 批注： pattern确实是真的不变式，但can_inv不是，因为这里有Sta.Dir.HeadPtr这样的单项右边等于数字的情况，这些数字与[]中的数字也有关系的
# /// 所以can_inv中的Sta.Dir.ShrSet[2] = false & Sta.Dir.ShrSet[1] = true 和pattern 中的Sta.UniMsg[2].Cmd = UNI_Nak & Sta.UniMsg[1].Cmd = UNI_None实际上并不是对称的

# False ['Sta.ShWbMsg.Proc != Sta.Dir.HeadPtr: 1, Sta.HomeProc.ProcCmd = NODE_None: 1, Sta.HomeProc.CacheState = CACHE_I: 1, Sta.Dir.Pending = false: 1, Sta.Dir.Dirty = false: 1, Sta.HomeProc.InvMarked = false: 1, Sta.Proc[_].CacheState = CACHE_I: 2, Sta.UniMsg[_].Cmd = UNI_None: 1, Sta.UniMsg[_].Cmd = UNI_Nak: 1, Sta.Dir.HomeHeadPtr = false: 1, Sta.Dir.HeadVld = true: 1, Sta.HomeUniMsg.Cmd = UNI_None: 1, Sta.Dir.Local = false: 1, Sta.ShWbMsg.Cmd = SHWB_None: 1, Sta.WbMsg.Cmd = WB_None: 1, Sta.Dir.ShrSet[_] = false: 1, Sta.Dir.ShrSet[_] = true: 1, Sta.Dir.HomeShrSet = false: 1, Sta.InvMsg[_].Cmd = INV_None: 2, Sta.NakcMsg.Cmd = NAKC_None: 1', 'NODE: 2']
# can_inv: !(Sta.Dir.HeadPtr = 2 & Sta.ShWbMsg.Proc = 1 & Sta.NakcMsg.Cmd = NAKC_None & Sta.InvMsg[2].Cmd = INV_None & Sta.InvMsg[1].Cmd = INV_None & Sta.Dir.HomeShrSet = false & Sta.Dir.ShrSet[2] = false & Sta.Dir.ShrSet[1] = true & Sta.WbMsg.Cmd = WB_None & Sta.ShWbMsg.Cmd = SHWB_None & Sta.Dir.Local = false & Sta.HomeUniMsg.Cmd = UNI_None & Sta.Dir.HeadVld = true & Sta.Dir.HomeHeadPtr = false & Sta.UniMsg[2].Cmd = UNI_Nak & Sta.UniMsg[1].Cmd = UNI_None & Sta.Proc[2].CacheState = CACHE_I & Sta.Proc[1].CacheState = CACHE_I & Sta.HomeProc.InvMarked = false & Sta.Dir.Dirty = false & Sta.Dir.Pending = false & Sta.HomeProc.CacheState = CACHE_I & Sta.HomeProc.ProcCmd = NODE_None)
# pattern  !(Sta.Dir.HeadPtr = 2 & Sta.ShWbMsg.Proc = 1 & Sta.NakcMsg.Cmd = NAKC_None & Sta.InvMsg[2].Cmd = INV_None & Sta.InvMsg[1].Cmd = INV_None & Sta.Dir.HomeShrSet = false & Sta.Dir.ShrSet[2] = true & Sta.Dir.ShrSet[1] = false & Sta.WbMsg.Cmd = WB_None & Sta.ShWbMsg.Cmd = SHWB_None & Sta.Dir.Local = false & Sta.HomeUniMsg.Cmd = UNI_None & Sta.Dir.HeadVld = true & Sta.Dir.HomeHeadPtr = false & Sta.UniMsg[2].Cmd = UNI_Nak & Sta.UniMsg[1].Cmd = UNI_None & Sta.Proc[2].CacheState = CACHE_I & Sta.Proc[1].CacheState = CACHE_I & Sta.HomeProc.InvMarked = false & Sta.Dir.Dirty = false & Sta.Dir.Pending = false & Sta.HomeProc.CacheState = CACHE_I & Sta.HomeProc.ProcCmd = NODE_None)






