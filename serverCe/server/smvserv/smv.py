#coding=utf-8

"""
Functions for checking invariants with NuSMV

@author Yongjian Li <lyj238@gmail.com>
@author Kaiqiang Duan <duankq@ios.ac.cn>
"""

import re
import sys
from pexpect import spawn, EOF, TIMEOUT


# max_bmc_check_num = 0


class SMV(object):
    def __init__(self, smv_path, smv_file, ord_file=None, timeout=None):
        super(SMV, self).__init__()
        self.smv_path = smv_path
        ord_switch = " -i %s" % ord_file if ord_file else ""
        self.process = spawn(smv_path + ord_switch + ' -dcx -int -old ' + smv_file)
        self.timeout = timeout
        self.diameter = None
        self.isComputing = False
        self.clear()

    def clear(self):
        self.process.expect([r'.*NuSMV\s+>\s+', EOF, TIMEOUT], timeout=.001)

    def go_and_compute_reachable(self):
        self.clear()
        if not self.diameter and not self.isComputing:
            self.isComputing = True
            self.process.send('go\ncompute_reachable\n')

    # def go_and_compute_reachable(self):
    #     self.clear()
    #     self.process.send('go\ncompute_reachable -k 5\n')
        # computed = self.process.expect(
        #     [r'The\s+number\s+of\s+performed\s+steps\s+is ', EOF, TIMEOUT], 
        #     timeout=0
        # )
        # while computed != 0:
        #     computed = self.process.expect(
        #     [r'The\s+number\s+of\s+performed\s+steps\s+is ', EOF, TIMEOUT], 
        #     timeout=0
        #     )
        
        # print(computed)
        # res = self.process.expect([r'\.\s+NuSMV\s+>\s+', EOF, TIMEOUT])
        # print(res)
        # if res == 0:
        #     length = self.process.before
        #     print(length)
        # print(self.process.after)
    
    def go_bmc(self):
        self.clear()
        self.process.send('go_bmc\nset bmc_length 15\n')    # flash
        # self.process.send('go_bmc\nset bmc_length 30\n')    # german
        return '0'

    def query_reachable(self):
        if self.diameter:
            return self.diameter
        computed = self.process.expect(
            [r'The\s+diameter\s+of\s+the\s+FSM\s+is ', EOF, TIMEOUT], 
            timeout=0
        )
        if computed == 2:
            return None
        elif computed == 0:
            res = self.process.expect([r'\.\s+NuSMV\s+>\s+', EOF, TIMEOUT])
            if res == 0:
                self.diameter = self.process.before
                return self.diameter
            return '-1'

    def check(self, invariant):
        self.clear()
        self.process.send('check_invar -p \"' + invariant + '\"\n')
        res = self.process.expect([r'--\s+invariant\s+.*\s+is\s+', 'ERROR:\s+', EOF, TIMEOUT],
            timeout=None)
        self.process.expect([r'\s*NuSMV\s+>\s+', EOF, TIMEOUT], timeout=self.timeout)
        if res == 0:
            return self.process.before.strip()
        return '0'
    
    def check_bmc(self, invariant):
        # global max_bmc_check_num
        to_check = invariant
        self.clear()
        self.process.send('check_ltlspec_bmc -p "G %s"\n'%invariant)
        res = self.process.expect([
                r'NuSMV\s+>\s+',
                r'ERROR:\s+', EOF, TIMEOUT
            ],
            timeout=None)

        if res == 0:
            output = self.process.before.strip()
            for o in output.decode().split('\n'):
                print("o:",o)
                # if o.startswith('-- no counterexample'):
                    # check_num = o.strip().split(' ')[-1]
                    # if int(check_num)>int(max_bmc_check_num):
                    #     max_bmc_check_num = check_num
                    #     print("max_bmc_check_num:",max_bmc_check_num)
                    #     with open("maxbmc.txt", "a") as file:
                    #         file.write(f"max_bmc_check_num:{max_bmc_check_num}")
                    #         file.write("\n")
                if o.startswith('-- specification'):
                    return o.strip().split(' ')[-1]
            if '-- specification' not in output.decode() and '-- no counterexample' not in output.decode():
                return self.check_bmc(invariant)
            return "true"
        return '0'

    def exit(self):
        self.process.send('quit\n')
        res = self.process.expect([EOF, TIMEOUT], timeout=self.timeout)
        self.process.terminate(force=True)
        return res == 0

    def go_and_compute_reachablebyK(self, k):
        self.clear()
        if not self.diameter and not self.isComputing:
            self.isComputing = True
            self.process.send(f'go\ncompute_reachable -k {k}\n')

    def go_and_compute_reachablebyT(self, t):
        self.clear()
        if not self.diameter and not self.isComputing:
            self.isComputing = True
            self.process.send(f'go\ncompute_reachable -t {t}\n')

if __name__ == '__main__':
    smv = SMV('/home/lyj238/NuSMV-2.6.0-Linux/bin/NuSMV', 'godsont.smv')
    # sys.stdout = open("switch" + '_bmc_check.log', 'w')
    res = smv.go_bmc()
    # print("res:",res)
    print(smv.check_bmc('!(node[1].cache[1].state = valid & node[1].firstRead[1] = FALSE & node[1].hasLock = TRUE & curNode = 1 & repRule = nlncr)'))



    # sys.stdout.close()


   