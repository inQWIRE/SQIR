class InvalidVOQCFunction(Exception):
    def __init__(self, inf, functions):
        self.func = inf
        self.functions = functions
        self.print_error = ("%s is not a valid VOQC optimization function. These are the 6 valid optimizers: %s" %(str(self.func), str(self.functions)))
        super().__init__(self.print_error)
	
class InvalidVOQCGate(Exception):
    def __init__(self, inf):
        self.gate = inf
        self.print_error = ("The gate: %s, is currently not supported in VOQC" % (self.gate))
        super().__init__(self.print_error)
	
