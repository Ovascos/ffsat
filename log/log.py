# inspired by https://stackoverflow.com/questions/48734950/use-multiple-output-stream-in-python

from enum import Enum

logger = {}


class LogTopic(Enum):
    TRACE = 1
    DEBUG = 2
    INFO = 3
    WARNING = 4
    ERROR = 5
    STAT = 6
    PROOF = 7


class FileLogger:
    def __init__(self, topic: LogTopic):
        self.topic = topic
        self.file = open(f"{topic.name.lower()}.log", 'w')

    def __call__(self, msg: str):
        self.file.write(msg + "\n")

    def __del__(self):
        self.file.flush()
        self.file.close()


class PrintLogger:
    class BColors:
        HEADER = '\033[95m'
        OKBLUE = '\033[94m'
        OKCYAN = '\033[96m'
        OKGREEN = '\033[92m'
        WARNING = '\033[93m'
        FAIL = '\033[91m'
        GRAY = '\033[0;37m'
        ENDC = '\033[0m'
        BOLD = '\033[1m'
        UNDERLINE = '\033[4m'

    colors = {
        LogTopic.ERROR: BColors.FAIL,
        LogTopic.WARNING: BColors.WARNING,
        LogTopic.STAT: BColors.OKCYAN,
        LogTopic.DEBUG: BColors.GRAY,
        LogTopic.TRACE: BColors.GRAY,
    }

    def __init__(self, topic: LogTopic):
        self.topic = topic
        self.color = self.colors[topic] if topic in self.colors.keys() else self.BColors.ENDC

    def __call__(self, msg: str):
        print(f"{self.color}{self.topic.name}: {msg}{self.BColors.ENDC}")


def enable_log(target: LogTopic, file: bool = False):
    global logger
    if target not in logger:
        logger[target] = FileLogger(target) if file else PrintLogger(target)


def disable_log(target: LogTopic):
    global logger
    if target in logger:
        del logger[target]


def log(topic: LogTopic, msg: str):
    global logger
    if topic in logger:
        logger[topic](msg)
