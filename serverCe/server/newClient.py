import socket
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


class Smv:
    class CannotCheck(Exception):
        pass

    host = '192.168.1.34'
    port = 50008

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



protocol_name = ""
table = {}

# 根据提供的协议，执行NuSMV计算可达集compute_reachable，并等待查询结果query_reachable
def set_context(name, smv_file_content, smv_ord=""):
    global protocol_name
    protocol_name = name
    _res = Smv.compute_reachable(name, smv_file_content, smv_ord)
    diameter = 0
    while diameter == 0:
        import time
        time.sleep(1)
        diameter = Smv.query_reachable(name)
    return diameter

def is_inv(inv=None, quiet=True):
    if inv in table:
        return table[inv]
    else:
        if protocol_name == "":
            raise Exception("Protocol name not set")
        else:
            r = Smv.check_inv(protocol_name, inv)
            table[inv] = r
            return r


def calculate_protocol_reachability(name, smv_file_content, smv_ord=""):
    s_t = time.time()
    diameter = set_context(name, smv_file_content, smv_ord)
    e_t = time.time()
    print(f"calculate the reachability with: {e_t - s_t} s.")
    print(f"Protocol {name} has a reachability diameter of {diameter}")

def check_invariants(name, invariants_list):
    for inv in invariants_list:
        is_true = is_inv(inv)
        print(f"Invariant '{inv}' is {'true' if is_true else 'false'} for protocol {name}")


if __name__ == "__main__":
    file_path = "server/smvserv/mutualEx.smv"

    smv_content = ""
    with open(file_path, "r") as file:
        smv_content = file.read()

    # print("smv_content:",smv_content)
    protocol_name = "mutualEx"
    calculate_protocol_reachability(protocol_name, smv_content)

    # invariant_list = ["n[1] = i", "n[1] = c -> n[2] != c", "!(n[2] = c & x = TRUE)",
                    #   "!(n[2] = c & n[1] = e)"]
    # check_invariants(protocol_name, invariant_list)




