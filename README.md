# <font style="color:rgb(31, 35, 40);">WiseParaVerifier</font>
---

<font style="color:rgb(31, 35, 40);">WiseParaVerifier is an automated tool to formally verify both cache coherence protocols and  distributed protocols by inferring inductive invariants. WiseParaVerifier supports the complex alternation of Forall and Exists quantifiers in parameterized invariants.</font>

## <font style="color:rgb(31, 35, 40);">Installation</font>
<font style="color:rgb(31, 35, 40);">WiseParaVerifier runs on Linux. It has been tested on Ubuntu 18.04.3 LTS, Ubuntu 20.04.3 LTS, and Rocky Linux 8.8.</font>

1. <font style="color:rgb(31, 35, 40);">Download and install Anaconda from </font>[<font style="color:rgb(31, 35, 40);">https://www.anaconda.com/products/individual</font>](https://www.anaconda.com/products/individual)<font style="color:rgb(31, 35, 40);">. Use version >= Python 3.8.</font>
2. <font style="color:rgb(31, 35, 40);">Install Python libraries</font>
+ z3 (0.2.0)
+ z3-solver (4.12.2.0)
+ lark (1.1.5)
3. <font style="color:rgb(31, 35, 40);">The Ivy verification tool only works on Python 2. Install it by</font>

```plain
$ conda create --name py2 python=2.7
$ conda activate py2
$ pip install ms-ivy
```

+ <font style="color:rgb(31, 35, 40);">Run</font><font style="color:rgb(31, 35, 40);"> </font>`<font style="color:rgb(31, 35, 40);">which ivy_check</font>`<font style="color:rgb(31, 35, 40);"> </font><font style="color:rgb(31, 35, 40);">to get the absolute path of the Ivy checker. We assume it is</font><font style="color:rgb(31, 35, 40);"> </font>`<font style="color:rgb(31, 35, 40);">ANACODNA_PATH/envs/py2/bin/ivy_check</font>`<font style="color:rgb(31, 35, 40);">.</font>
+ <font style="color:rgb(31, 35, 40);">Append the following line to</font><font style="color:rgb(31, 35, 40);"> </font>`<font style="color:rgb(31, 35, 40);">~/.bashrc</font>`

```plain
alias ivy_check="ANACODNA_PATH/envs/py2/bin/ivy_check"
```

4. <font style="color:rgb(31, 35, 40);">WiseParaVerifier using NuSMV or Murphi as a Model Checker. In fact, we usually choose NuSMV as our model checker because it includes reachability analysis and BMC, which meet all our requirements. However, WiseParaVerifier use protocols modeled by Murphi as standard input, so it is recommended that you also install Murphi so that you can provide correct Murphi protocols descriptions in your new experiments.</font>
    1. <font style="color:rgb(31, 35, 40);">install Murphi by</font>

<font style="color:rgb(31, 35, 40);">Download the cmurphi zip from the following link and unzip it into a local folder: </font>[http://mclab.di.uniroma1.it/site/index.php/software/18-cmurphi](http://mclab.di.uniroma1.it/site/index.php/software/18-cmurphi)<font style="color:rgb(31, 35, 40);">. Then</font>

```plain
cd ./src
make
```

    2. <font style="color:rgb(31, 35, 40);">install NuSMV-2.6.0 by</font>

<font style="color:rgb(31, 35, 40);">Download the binary version directly from: </font>[https://nusmv.fbk.eu/downloads.html](https://nusmv.fbk.eu/downloads.html)<font style="color:rgb(31, 35, 40);">, and extracting it to obtain four directories - </font>`<font style="color:rgb(0, 0, 0);background-color:rgb(247, 247, 247);">bin</font>`<font style="color:rgb(31, 35, 40);">, </font>`<font style="color:rgb(0, 0, 0);background-color:rgb(247, 247, 247);">include</font>`<font style="color:rgb(31, 35, 40);">, </font>`<font style="color:rgb(0, 0, 0);background-color:rgb(247, 247, 247);">lib</font>`<font style="color:rgb(31, 35, 40);">, and </font>`<font style="color:rgb(0, 0, 0);background-color:rgb(247, 247, 247);">share</font>`<font style="color:rgb(31, 35, 40);"> - allows for use without compilation.</font>

<font style="color:rgb(31, 35, 40);">After installation, set the paths of SMV_PATH, MU_PATH, MU_INCLUDE in sever/settings.py.</font>

---

## <font style="color:rgb(31, 35, 40);">Usage</font>
<font style="color:rgb(31, 35, 40);">Given a Murphi description of a protocol and its safety property, WiseParaVerifier automatically constructs several </font>![image](https://cdn.nlark.com/yuque/__latex/7aaf2781990aa336d909f7ebd32e2f69.svg)<font style="color:rgb(31, 35, 40);">needed for verification. It then obtains a set of concrete auxiliary invariants through </font>_**<font style="color:rgb(31, 35, 40);">generalization</font>**_<font style="color:rgb(31, 35, 40);"> and </font>_**<font style="color:rgb(31, 35, 40);">symmetry</font>**_<font style="color:rgb(31, 35, 40);">. Finally, these invariants are promoted to </font>_**<font style="color:rgb(31, 35, 40);">parameterized</font>**_<font style="color:rgb(31, 35, 40);"> invariants, which supporting the alternating use of universal and existential quantifiers.</font>

<font style="color:rgb(31, 35, 40);">To automatically complete the verification process using WiseParaVerifier, </font>

<font style="color:rgb(31, 35, 40);">first, you need to start the server-side NuSMV service: </font>

```plain
cd serverCe
python3 server/server.py
```

<font style="color:rgb(31, 35, 40);">The server-side only needs to be started once, and it can continue to provide service until you manually shut it down or encounter an unexpected event. Additionally, NuSMV will remember the previously computed reachability, meaning that for every protocol, you only need to calculate the reachability once to perform unlimited verifications.</font>

<font style="color:rgb(31, 35, 40);">Then, here is a sample configuration file </font>`<font style="color:rgb(0, 0, 0);background-color:rgb(247, 247, 247);">CONFIG</font>`<font style="color:rgb(31, 35, 40);"> where the first line specifies whether you want the invariants to be existentially quantified and the second line indicates whether you want to use the heuristic generalize:</font>

```plain
EXISTENTIAL_QUANTIFICATION = True
USE_HEURISTIC_GENERALIZE = True
```

<font style="color:rgb(31, 35, 40);">If the </font>`<font style="color:rgb(0, 0, 0);background-color:rgb(247, 247, 247);">CONFIG</font>`<font style="color:rgb(31, 35, 40);"> file is not set, the default behavior is as follows:</font>

+ <font style="color:rgb(31, 35, 40);">Existential quantification is not used by default as it introduces higher computational overhead.</font>
+ <font style="color:rgb(31, 35, 40);">Heuristic generalize is used by default as it enhances the verification efficiency.</font>

<font style="color:rgb(31, 35, 40);">Lastly, you only need to input the name of the protocol to automatically complete the verification process. For example: </font>

```plain
python3 wiseParaVerifier/invFinder.py client_server_db_ae
```

<font style="color:rgb(31, 35, 40);">As suggested on the screen, the concrete inductive invariants are written to: client_server_db_ae/client_server_db_ae_invs.txt,  and the corresponding parameterized invariants and the protocol's Ivy description are located in client_server_db_ae/client_server_db_ae_proved.ivy.</font>

---

## <font style="color:rgb(31, 35, 40);">Structure</font>
+ <font style="color:rgb(31, 35, 40);">protocols/: The protocol for verification, including .m, .smv, and .ivy formats.</font>
+ <font style="color:rgb(31, 35, 40);">wiseParaVerifier/: The python source code for verification.</font>
    - <font style="color:rgb(31, 35, 40);">concreteF.py: Read the .m file of the protocol, build its Python syntax tree; instantiate all rules and safety properties of the protocol according to the given number of instances; analyze the relationships between all rule and safety property instances, then construct and filter verification formulas F. Used by </font>invFinder.py.
    - <font style="color:rgb(31, 35, 40);">invFinder.py: Solve formula F to obtain CTI; generalize specific auxiliary invariants based on CTI; accelerate space reduction using symmetry techniques, and combine symmetry & quantification to promote invariants to parameterized form.</font>
+ <font style="color:rgb(31, 35, 40);">client.py: Responsible for socket communication, forwarding the invariants to be verified to the server and retrieving the verification results. Used by </font>invFinder.py.
+ <font style="color:rgb(31, 35, 40);">murphi.py: Build Python Abstract Syntax Trees for the Murphi models, translate Murphi models to NuSMV and Ivy models.</font>
+ <font style="color:rgb(31, 35, 40);">murphiparser.py: Parsing protocols modeled in Murphi. Used by murphi.py.</font>

---

## <font style="color:rgb(31, 35, 40);">Assessment</font>
<font style="color:rgb(31, 35, 40);">The table below lists the experimental results of all cache coherence protocols and distributed protocols in our benchmark, including verification time and the number of parameterized invariants.</font>

| <font style="color:rgb(31, 35, 40);">protocol name</font> | <font style="color:rgb(31, 35, 40);">safety properties</font> | <font style="color:rgb(31, 35, 40);">parameterized invariants</font> | <font style="color:rgb(31, 35, 40);">running time (s)</font> |
| --- | :---: | :---: | :---: |
| <font style="color:rgb(31, 35, 40);">mutualEx</font> | <font style="color:#000000;">1 </font> | <font style="color:#000000;">4</font> | <font style="color:#000000;">1.4s</font> |
| <font style="color:#000000;">mutdata</font> | <font style="color:#000000;">2 </font> | <font style="color:#000000;">6</font> | <font style="color:#000000;">2.9s</font> |
| <font style="color:#000000;">mutualEx_M2</font> | <font style="color:#000000;">2 </font> | <font style="color:#000000;">13</font> | <font style="color:#000000;">17.1</font> |
| <font style="color:#000000;">germanNodata</font> | <font style="color:#000000;">1 </font> | <font style="color:#000000;">39</font> | <font style="color:#000000;">19.1</font> |
| <font style="color:#000000;">german</font> | <font style="color:#000000;">2</font> | <font style="color:#000000;">55</font> | <font style="color:#000000;">49.2</font> |
| <font style="color:#000000;">flashNodata</font> | <font style="color:#000000;">2 </font> | <font style="color:#000000;">97</font> | <font style="color:#000000;">329</font> |
| <font style="color:#000000;">flash</font> | <font style="color:#000000;">4 </font> | <font style="color:#000000;">131</font> | <font style="color:#000000;">585</font> |
| <font style="color:#000000;">decentralized_lock</font> | <font style="color:#000000;">1 </font> | <font style="color:#000000;">15</font> | <font style="color:#000000;">4.6</font> |
| <font style="color:#000000;">lock_server</font> | <font style="color:#000000;">1 </font> | <font style="color:#000000;">1</font> | <font style="color:#000000;">0.2</font> |
| <font style="color:#000000;">multi_lock_server</font> | <font style="color:#000000;">1 </font> | <font style="color:#000000;">11</font> | <font style="color:#000000;">2.5</font> |
| <font style="color:#000000;">Ricart-Agrawala</font> | <font style="color:#000000;">1 </font> | <font style="color:#000000;">2</font> | <font style="color:#000000;">0.4</font> |
| <font style="color:#000000;">shard</font> | <font style="color:#000000;">1 </font> | <font style="color:#000000;">13</font> | <font style="color:#000000;">3.5</font> |
| <font style="color:#000000;">client_server_ae(exists)</font> | <font style="color:#000000;">1 </font> | <font style="color:#000000;"> 2</font> | <font style="color:#000000;">3.2</font> |
| <font style="color:#000000;">client_server_db_ae(exists)</font> | <font style="color:#000000;">1 </font> | <font style="color:#000000;">8</font> | <font style="color:#000000;">6.8</font> |
| <font style="color:#000000;">toy_consensus_epr(exists)</font> | <font style="color:#000000;">1 </font> | <font style="color:#000000;">4</font> | <font style="color:#000000;">4.9</font> |
| <font style="color:#000000;">consensus_epr(exists)</font> | <font style="color:#000000;">1 </font> | <font style="color:#000000;">16</font> | <font style="color:#000000;">63.1</font> |
| <font style="color:#000000;">two_phase_commit</font> | <font style="color:#000000;">1</font> | <font style="color:#000000;">10</font> | <font style="color:#000000;">4.2</font> |
















