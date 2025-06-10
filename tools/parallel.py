# Concurrency support for toolchain

import sys
import threading
import queue


class Printer:
    lock = None

    def __init__(self):
        self.lock = None

    def activate(self):
        self.lock = threading.Lock()

    def fix(self, line):
        if len(line) == 0 or line[-1] != '\n':
            return line + '\n'
        else:
            return line

    def print(self, line):
        nline = self.fix(line)
        if self.lock is None:
            sys.stdout.write(nline)
        else:
            self.lock.acquire()
            sys.stdout.write(nline)
            self.lock.release()
    
class Scheduler:
    queue = None
    workers = []
    
    def __init__(self, limit):
        self.queue = queue.Queue()
        self.workers = []
        self.jcount = 0
        self.jlock = threading.Lock()
        while len(self.workers) < limit:
            t = threading.Thread(target=self.work, daemon=True)
            self.workers.append(t)
            t.start()

    def schedule(self, j):
        self.queue.put(j)
            
    def work(self):
        while True:
            j = self.queue.get()
            j.run()
            self.queue.task_done()

    def wait(self):
        self.queue.join()
        
## Testing code
## 
## # Needed for testing
## import datetime
## import random
## import time
## 
## class TestJob:
## 
##     queueTime = None
##     id = None
##     duration = None
##     printer = None
## 
##     def __init__(self, id, printer):
##         self.queueTime = datetime.datetime.now()
##         self.id = id
##         self.duration = 5 * random.random()
##         self.printer = printer
##         
##     def run(self):
##         startTime = datetime.datetime.now()
##         time.sleep(self.duration)
##         self.printer.print("JOB #%d.  Duration %.6f, Queued at %s.  Started at %s.  Completed at %s" %
##                            (self.id, self.duration, str(self.queueTime), str(startTime), str(datetime.datetime.now())))
## 
## def test(nthread, njob):
##     p = Printer()
##     p.activate()
##     p.print("CENTRAL: Scheduling %d jobs with %d threads" % (njob, nthread))
##     s = Scheduler(nthread)
##     for jid in range(njob):
##         j = TestJob(jid+1, p)
##         s.schedule(j)
##     p.print("CENTRAL: Waiting for jobs to complete")
##     s.wait()
##     p.print("CENTRAL: Done")
