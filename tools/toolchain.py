#!/usr/bin/python3

#####################################################################################
# Copyright (c) 2023 Randal E. Bryant, Carnegie Mellon University
# Last edit: May 19, 2022
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
# associated documentation files (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge, publish, distribute,
# sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all copies or
# substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
# NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
# DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
# OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
########################################################################################

# Run verification toolchain for projected knowledge compilation

import getopt
import sys
import os.path
import subprocess
import datetime
import time

import parallel

p = parallel.Printer()

def usage(name):
    p.print("Usage: %s [-h] [-v VERB] [-t TIME] [-n NDEL] [-l NFILE] [FILE.EXT ...]" % name)
    p.print("  -h       Print this message")
#    p.print("  -x       Exit after first error (including timeout)")
#    p.print("  -R       Remove all generated files")
    p.print("  -v       Set verbosity level")
#    p.print("  -F       Generate & check forward implication proof only")
#    p.print("  -m MODE  Generation mode: monolithic (m), structured (s), hybrid (h)")
#    p.print("  -L       Expand each node, rather than using lemmas")
#    p.print("  -G       Prove each literal separately, rather than grouping into single proof")
#    p.print("  -P PRE   Specify preprocessing level: (0:None, 1:+BCP, 2:+Pure lit, >=3:+BVE(P-2)");
#    p.print("  -T TSE   Specify use of Tseitin variables (n=none, d=detect, p=promote)");
    p.print("  -t TIME  Limit time for each of the programs")
#    p.print("  -N NMAC  Specify number of macro threads")
    p.print("  -n NDEL  Specify deletion threads")
    p.print("  -l NFILE Specify file containing root names")
    p.print("  EXT      Can be any extension for wild-card matching (e.g., cnf, nnf)")

# Blocking file.  If present in directory, won't proceed.  Recheck every sleepTime seconds
blockPath = "./block.txt"
sleepTime = 60

# Defaults
standardTimeLimit = 600

# Possible return codes
underReturnCode = 10
overReturnCode = 20

verbLevel = 2
cleanup = False
exitWhenError = False
forwardOnly = False
foundOverCount = False
monolithic_threshold = 1000 * 1000
tree_ratio_threshold = 5.0
mode = 'h'
useLemma = True
group = True

# Threading used when set to number
macroThreadCount = None
deletionThreadCount = 7

nameFile = None

#timeLimits = { "D4" : 4000, "GEN" : 1000, "FCHECK" : 1000, "LCHECK" : 1000 }
timeLimits = { "D4" : 2000, "GEN" : 10000, "FCHECK" : 30000, "LCHECK" : 10000}

clauseLimit = (1 << 31) - 1

commentChar = 'c'

# Pathnames
def genProgramPath(progName, subdirectory):
    ppath = os.path.abspath(__file__)
    parts = ppath.split('/')
    if len(parts) >= 2:
        parts[-2] = subdirectory
        parts[-1] = progName
    npath = "/".join(parts)
    if not os.path.exists(npath):
        raise Exception("Couldn't find program '%s'" % npath)
    return npath


# Track files to be deleted
cleanupFiles = []

def doCleanup():
    if not cleanup:
        return
    for fname in cleanupFiles:
        try:
            os.remove(fname)
        except:
            continue

def trim(s):
    while len(s) > 0 and not s[0].isalnum():
        s = s[1:]
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

def setTimeLimit(t):
    global timeLimits
    global standardTimeLimit
    standardTimeLimit = t
    for key in timeLimits.keys():
        timeLimits[key] = t

def waitWhileBlocked():
    first = True
    while os.path.exists(blockPath):
        if first:
            p.print("Waiting to unblock")
        first = False
        time.sleep(sleepTime)

def checkFile(prefix, fname, logFile):
    f = open(fname, 'r')
    bytes = 0
    lines = 0
    for line in f:
        if len(line) > 0 and line[0] == commentChar:
            continue
        bytes += len(line)
        lines += 1
    p.print("%s: LOG: size %s %d lines %d bytes" % (prefix, fname, lines, bytes))
    logFile.write("%s: LOG: size %s %d lines %d bytes\n" % (prefix, fname, lines, bytes))
    f.close()

def cleanString(s):
    res = ""
    for c in s:
        if c == '\n' or c.isprintable():
            res = res + c
    return res
        

def runProgram(prefix, root, commandList, logFile, extraLogName = None):
    returnCode = 0
    if prefix in timeLimits:
        timeLimit = timeLimits[prefix]
    else:
        timeLimit = standardTimeLimit
    result = ""
    cstring = " ".join(commandList)
    p.print("%s. %s: Running '%s' with time limit of %d seconds" % (root, prefix, cstring, timeLimit))
    logFile.write("%s LOG: Running %s\n" % (prefix, cstring))
    logFile.write("%s LOG: Time limit %d seconds\n" % (prefix, timeLimit))
    start = datetime.datetime.now()
    try:
        cp = subprocess.run(commandList, capture_output = True, timeout=timeLimit, text=True)
    except subprocess.TimeoutExpired as ex:
        # Incorporate information recorded by external logging
        if (extraLogName is not None):
            try:
                xlog = open(extraLogName, "r")
                for line in xlog:
                    line = cleanString(line)
                    logFile.write(line)
                xlog.close()
            except:
                pass
        p.print("%s. %s Program timed out after %d seconds" % (root, prefix, timeLimit))
        result += "%s ERROR: Timeout after %d seconds\n" % (prefix, timeLimit)
        delta = datetime.datetime.now() - start
        seconds = delta.seconds + 1e-6 * delta.microseconds
        result += "%s LOG: Elapsed time = %.3f seconds\n" % (prefix, seconds)
        result += "%s OUTCOME: Timeout\n" % (prefix)
        logFile.write(result)
        return (False, 1)
    ok = True
    returnCode = cp.returncode
    if returnCode != 0:
        result += "%s ERROR: Return code = %d\n" % (prefix, cp.returncode)
        ok = False
    outcome = "normal" if ok else "failed"
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    result += "%s LOG: Elapsed time = %.3f seconds\n" % (prefix, seconds)
    result += "%s OUTCOME: %s\n" % (prefix, outcome)
    p.print("%s. %s: OUTCOME: %s" % (root, prefix, outcome))
    p.print("%s. %s: Elapsed time: %.3f seconds" % (root, prefix, seconds))
    logFile.write(cleanString(cp.stdout))
    logFile.write(result)
    return (ok, returnCode)

def stripComments(inCnfName, outCnfName):
    try:
        infile = open(inCnfName, "r")
    except:
        logFile.write("Couldn't open input CNF file '%s'\n" % inCnfName)
        return False
    try:
        outfile = open(outCnfName, "w")
    except:
        logFile.write("Couldn't open output CNF file '%s'\n" % outCnfName)
        close(infile)
        return False
    for line in infile:
        while len(line) > 0 and line[0] in " \t":
            line = line[1:]
        if len(line) > 0 and line[0] != 'c':
            outfile.write(line)
    infile.close()
    outfile.close()
    return True

def cnfNamer(root, home):
    suffix = ".cnf"
    return home + "/" + root + suffix

def nnfNamer(root, home):
    suffix = "nnf" if forwardOnly else "snnf"
    return home + "/" + root + "." + suffix

def cpogNamer(root, home):
    extension = ""
    if not forwardOnly:
        extension += "s"
    extension += "cpog"
    cpogName = home + "/" + root + "." + extension
    return cpogName

# Only run D4 if don't yet have .nnf file
def runD4(root, home, logFile, force):
    cnfName = cnfNamer(root, home)
    nnfName = nnfNamer(root, home)
    if not force and os.path.exists(nnfName):
        return True
    cmd = [genProgramPath("d4v2-mod", "d4v2-modified"), '--input', cnfName, '-m', 'ddnnf-compiler']
    if not forwardOnly:
        cmd += ['--skolem', 'on']
    cmd += ['--dump-ddnnf',  nnfName]
    prefix = "D4"
    ok = runProgram(prefix, root, cmd, logFile)[0]
    if ok:
        checkFile(root + ". D4 NNF", nnfName, logFile)
    cleanupFiles.append(nnfName)
    return ok

def runGen(root, home, logFile, force):
    global monolithic_threshold, tree_ratio_threshold, foundOverCount
    if mode == 'm':
        monolithic_threshold = -1
        tree_ratio_threshold = 1e12
    elif mode == 's':
        monolithic_threshold = 1
        tree_ratio_threshold = 0
    extraLogName = "generate.log"
    cnfName = cnfNamer(root, home)
    nnfName = nnfNamer(root, home)
    cpogName = cpogNamer(root, home)
#    if not force and os.path.exists(cpogName):
#        return True
    cmd = [genProgramPath("cpog-generate", "cpog/generator")]
    cmd += ["-v", str(verbLevel)]
    if forwardOnly:
        cmd += ['-a', 'f']
    cmd += ['-m', str(monolithic_threshold), '-r', str(tree_ratio_threshold)]
    cmd += ["-C", str(clauseLimit), "-L", extraLogName, cnfName, nnfName, cpogName]
    ok, returnCode = runProgram("GEN", root, cmd, logFile, extraLogName = extraLogName)
    if ok:
        checkFile(root + ". GEN", cpogName, logFile)
#    cleanupFiles.append(cpogName)
    return ok

def runCheck(root, home, logFile):
    cnfName = cnfNamer(root, home)
    cpogName = cpogNamer(root, home)
    extraLogName = "check.log"
    cmd = [genProgramPath("cpog-check", "cpog/checker")]
    cmd += ["-v", str(verbLevel)]
    cmd += ["-L", extraLogName]
    if deletionThreadCount > 1:
        cmd += ["-n", str(deletionThreadCount)]
    if forwardOnly:
        cmd += ['-D']
    cmd += [cnfName, cpogName]
    ok =  runProgram("CHECK", root, cmd, logFile, extraLogName = extraLogName)[0]
    return ok

def runCake(root, home, logFile):
    cnfName = cnfNamer(root, home)
    cpogName = cpogNamer(root, home)
    cmd = [genProgramPath("cake_scpog", "cake_scpog")]
    cmd += [cnfName, cpogName]
    ok = runProgram("CAKEML", root, cmd, logFile)
    return ok


def runSequence(home, root, force):
    waitWhileBlocked()
    result = ""
    prefix = "OVERALL"
    start = datetime.datetime.now()
    extension = "log"
    if forwardOnly:
        extension = "forward_" + extension
    prefix = "mono_" if mode == 'm' else "structured_" if mode == 's' else ""
    extension = prefix + extension
    logName = root + "." + extension
    if not force and os.path.exists(logName):
        p.print("Already have file %s.  Skipping benchmark" % logName)
        return True
    try:
        logFile = open(logName, 'w')
    except:
        p.print("%s. %s ERROR:Couldn't open file '%s'" % (root, prefix, logName))
        return False
    ok = True
    done = False
    ok = runD4(root, home, logFile, force)
    ok = ok and runGen(root, home, logFile, force)
    ok = ok and runCheck(root, home, logFile)
    ok = ok and runCake(root, home, logFile)
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    result += "%s LOG: Elapsed time = %.3f seconds\n" % (prefix, seconds)
    outcome = "normal" if ok else "failed"
    result += "%s OUTCOME: %s\n" % (prefix, outcome)
    p.print("%s. %s OUTCOME: %s" % (root, prefix, outcome))
    p.print("%s. %s Elapsed time: %.3f seconds" % (root, prefix, seconds))
    p.print("%s. %s Logfile at %s" % (root, prefix, logName))
    logFile.write(result)
    logFile.close()
    doCleanup()
    return ok

def stripSuffix(fname):
    fields = fname.split(".")
    if len(fields) > 1:
        fields = fields[:-1]
    return ".".join(fields)

class Job:
    home = None
    root = None
    force = None

    def __init__(self, home, root, force):
        self.home = home
        self.root = root
        self.force = force

    def run(self):
        runSequence(self.home, self.root, self.force)


def runBatch(home, fileList, force):
    roots = [stripSuffix(f) for f in fileList]
    roots = [r for r in roots if r is not None]
    p.print("Running on roots %s" % roots)
    if macroThreadCount is None:
        for r in roots:
            if not runSequence(home, r, force) and exitWhenError:
                p.print("Error encountered.  Exiting")
                return
    else:
        s = parallel.Scheduler(macroThreadCount)
        p.activate()
        for r in roots:
            j = Job(home, r, force)
            s.schedule(j)
        s.wait()

def run(name, args):
    global verbLevel, nameFile
    global deletionThreadCount
    home = "."
    force = True
    optList, args = getopt.getopt(args, "hv:t:l:n:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            return
        if opt == '-v':
            verbLevel = int(val)
        elif opt == '-n':
            deletionThreadCount = int(val)
        elif opt == '-t':
            setTimeLimit(int(val))
        elif opt == '-l':
            nameFile = val
        else:
            p.print("Unknown option '%s'" % opt)
            usage(name)
            return
    fileList = args
    if nameFile is not None:
        try:
            nfile = open(nameFile, 'r')
        except:
            p.print("Couldn't open name file '%s'" % nameFile)
            usage(name)
            return
        for line in nfile:
            fname = trim(line)
            fileList.append(fname)
        nfile.close()
            
    runBatch(home, fileList, force)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    sys.exit(0)

