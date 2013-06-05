import json

class Continuation(object):
    def __init__(self, fun, next):
        self.fun = fun
        self.next = next

def isContinuation(x): return isinstance(x, Continuation)

class Capture(object):
    def __init__(self, prompt, handler):
        self.prompt = prompt
        self.handler = handler
        self.k = None

def isCapture(x): return isinstance(x, Capture)
def captureFrame(capture, fun): capture.k = Continuation(fun, capture.k)
def continueFrame(k, f): return k.fun(k.next, f)
    
# Evaluation Core
def evaluate(e, k, f, x):
    if hasattr(x, 'wat_eval'): return x.wat_eval(e, k, f)
    else: return x

class Sym(object):
    def __init__(self, name): self.name = name
    def wat_eval(self, e, k, f): return lookup(e, self.name)
    def wat_match(self, e, rhs):
        if e is None: fail("undefined argument: " + self.name)
        e.bindings[self.name] = rhs
        return e.bindings[self.name]
    def __str__(self): return ":"+self.name

class Cons(object):
    def __init__(self, car, cdr):
        self.car = car
        self.cdr = cdr
    def wat_eval(self, e, k, f):
        if isContinuation(k): op = continueFrame(k, f)
        else: op = evaluate(e, None, None, car(self))    
        if isCapture(op):
            other = self
            captureFrame(op, lambda k,f: that.wat_eval(e, k, f))
            return op
        return combine(e, None, None, op, cdr(self))    
    def wat_match(self, e, rhs):
        car(self).wat_match(e, car(rhs))
        cdr(self).wat_match(e, cdr(rhs))        
    def __str__(self): return str(self.car) + ', ' + str(self.cdr) 
        
# Operative & Applicative Combiners
def combine(e, k, f, cmb, o):
    if hasattr(cmb, 'wat_combine'): return cmb.wat_combine(e, k, f, o);
    else: fail("not a combiner: " + str(cmb))

class Opv(object):
    def __init__(self, p, ep, x, e):
        self.p, self.ep, self.x, self.e = p, ep, x, e
    def wat_combine(self, e, k, f, o):
        xe = make_env(self.e)
        bind(xe, self.p, o)
        bind(xe, self.ep, e)
        return evaluate(xe, k, f, self.x)

def wrap(cmb): return Apv(cmb)
def unwrap(apv): return apv.cmb

class Apv(object):
    def __init__(self, cmb): self.cmb = cmb
    def wat_combine(self, e, k, f, o):
        if isContinuation(k): args = continueFrame(k, f)
        else: args = evalArgs(e, None, None, o, NIL)
        if isCapture(args):
            other = self    
            captureFrame(args, lambda k,f: that.wat_combine(e, k, f, o))
            return args
        return self.cmb.wat_combine(e, None, None, args);
    def __str__(self): return '(Apv ' + str(self.cmb) + ')'
 
def evalArgs(e, k, f, todo, done):
    if todo is NIL: return reverse_list(done)
    if isContinuation(k): arg = continueFrame(k, f)
    else: arg = evaluate(e, None, None, car(todo))    
    if isCapture(arg):
        captureFrame(arg, lambda k,f: evalArgs(e, k, f, todo, done))
        return arg        
    return evalArgs(e, None, None, cdr(todo), cons(arg, done))

# Built-in Combiners 
class __Vau(object):
    def wat_combine(self, e, k, f, o):
        return Opv(elt(o, 0), elt(o, 1), elt(o, 2), e)
    def __str__(self): return '__Vau'

class Def(object):    
    def wat_combine(self, e, k, f, o):
        if isContinuation(k): val = continueFrame(k, f)
        else: val = evaluate(e, None, None, elt(o, 1))
        if isCapture(val):    
            captureFrame(val, lambda k,f: self.wat_combine(e, k, f, o))
            return val
        return bind(e, elt(o, 0), val)
    def __str__(self): return 'Def'

class Eval(object):        
    def wat_combine(self, e, k, f, o):
        return evaluate(elt(o, 1), k, f, elt(o, 0))
        
# First-order Control 
class Begin(object):
    def wat_combine(self, e, k, f, o):
        if o is NIL: return None
        else: return begin(e, k, f, o)
    def __str__(self): return 'Begin'

def begin(e, k, f, xs):
    if isContinuation(k): res = continueFrame(k, f)
    else: res = evaluate(e, None, None, car(xs))    
    if isCapture(res):
        captureFrame(res, lambda k,f: begin(e, k, f, xs))
        return res
    kdr = cdr(xs)
    if kdr is NIL: return res
    else: return begin(e, None, None, kdr)

class If(object):    
    def wat_combine(self, e, k, f, o):
        if isContinuation(k): test = continueFrame(k, f)
        else: test = evaluate(e, None, None, elt(o, 0))   
        if isCapture(test):
            captureFrame(test, lambda k,f: self.wat_combine(e, k, f, o))
            return test
        if test: return evaluate(e, None, None, elt(o, 1))
        else:    return evaluate(e, None, None, elt(o, 2))    

class __Loop(object):
    def wat_combine(self, e, k, f, o):
        first = True
        while True:
            if first and isContinuation(k): res = continueFrame(k, f)
            else: res = evaluate(e, None, None, elt(o, 0))
            first = false
            if isCapture(res):
                captureFrame(res, lambda k, f: self.wat_combine(e, k, f, o))
                return res

class __Catch(object):
    def wat_combine(self, e, k, f, o):
        th = elt(o, 0)
        handler = elt(o, 1)
        try:
            if isContinuation(k): res = continueFrame(k, f)
            else: res = combine(e, None, None, th, NIL)    
        except Exception as exc:        
            # unwrap handler to prevent eval if exc is sym or cons
            res = combine(e, None, None, unwrap(handler), _list(exc))
        if isCapture(res):
            captureFrame(res, lambda k,f: self.wat_combine(e, k, f, o))
        return res

class Finally(object):
    def wat_combine(self, e, k, f, o):
        prot, cleanup  = elt(o, 0), elt(o, 1)
        try:
            if isContinuation(k): res = continueFrame(k, f)
            else: res = evaluate(e, None, None, prot)
            if isCapture(res):
                captureFrame(res, lambda k, f: self.wat_combine(e, k, f, o))
        finally:                
            if isCapture(res): return res
            else: return doCleanup(e, None, None, cleanup, res)

def doCleanup(e, k, f, cleanup, res):
    if isContinuation(k): fres = continueFrame(k, f)
    else: fres = evaluate(e, None, None, cleanup)
    if isCapture(fres):
        captureFrame(fres, lambda k,f: doCleanup(e, k, f, cleanup, res))
        return fres
    else:    
        return res

# Delimited Control
class __PushPrompt(object):
    def wat_combine(self, e, k, f, o):
        prompt, th = elt(o, 0), elt(o, 1)
        if isContinuation(k): res = continueFrame(k, f)
        else: res = combine(e, None, None, th, NIL)
        if isCapture(res):
            if res.prompt is prompt:
                continuation = res.k
                handler = res.handler
                return combine(e, None, None, handler, cons(continuation, NIL))
            else:
                captureFrame(res, lambda k, f: self.wat_combine(e, k, f, o))
                return res
        else:
            return res

class __TakeSubcont(object):
    def wat_combine(self, e, k, f, o):
        prompt, handler = elt(o, 0), elt(o, 1)
        cap = Capture(prompt, handler)
        captureFrame(cap, lambda k, thef: combine(e, None, None, thef, NIL))
        return cap

class __PushSubcont(object):
    def wat_combine(self, e, k, f, o):
        thek, thef = elt(o, 0), elt(o, 1)
        if isContinuation(k): res = continueFrame(k, f)
        else: res = continueFrame(thek, thef)
        if isCapture(res):
            captureFrame(res, lambda k, f: self.wat_combine(e, k, f, o))
        return res

# Dynamic Variables
class DV(object):
    def __init__(self, val): self.val = val

class DNew(object):
    def wat_combine(self, e, k, f, o): return DV(elt(o, 0))

class DRef(object):
    def wat_combine(self, e, k, f, o): return elt(o, 0).val

class __DLet(object):
    def wat_combine(self, e, k, f, o):
        dv, val, th = elt(o, 0), elt(o, 1), elt(o, 2)
        oldVal = dv.val
        dv.val = val
        try:
            if isContinuation(k): res = continueFrame(k, f)
            else: res = combine(e, None, None, th, NIL)
            if isCapture(res):
                captureFrame(res, lambda k, f: self.wat_combine(e, k, f, o))
            return res
        finally:
            dv.val = oldVal
                
# Objects
class Nil(object):
    def wat_match(self, e, rhs):
        if rhs is not NIL: fail("NIL expected, but got: " + json.dumps(rhs))
    def __str__(self): return 'null'

NIL = Nil()
class Ign(object):
    def wat_match(self, e, rhs): pass
    def __str__(self): return '#ignore'
IGN = Ign()

def cons(car, cdr): return Cons(car, cdr)
def car(cons): return cons.car
def cdr(cons): return cons.cdr
def elt(cons, i):
    if i == 0: return car(cons)
    else: return elt(cdr(cons), i - 1)
def sym_name(sym): return sym.name        

class Env(object):
    def __init__(self, parent):
        if parent is not None: self.bindings = dict(parent.bindings)
        else: self.bindings = dict()
    #def __str__(self): return json.dumps(self.bindings)        
    def __str__(self): return str(self.bindings)
    
def make_env(parent = None): return Env(parent)
def lookup(e, name):
    try: return e.bindings[name]
    except KeyError: fail("unbound: " + name)

def bind(e, lhs, rhs):
    lhs.wat_match(e, rhs);
    return rhs
            
# Utilities
def fail(err): raise Exception(err)
def _list(*args): return array_to_list(args)
def list_star(*args):
    length = len(args)
    if length >= 1: c = args[-1]
    else: c = NIL
    i = length - 1
    while i > 0:
        c = cons(args[i - 1], c)
        i -= 1
    return c

def array_to_list(array, end = None):
    c = end and end or NIL
    i = len(array)
    while i > 0:
        c = cons(array[i - 1], c)
        i -= 1
    return c

def list_to_array(c):
    res = []
    while c is not NIL:
        res.append(car(c))
        c = cdr(c)
    return res

def reverse_list(l):
    res = NIL
    while l is not NIL:
        res = cons(car(l), res)
        l = cdr(l)
    return res

# Parser 
def parse_json_value(obj):
    if type(obj) == type('str'):
        if obj == "#ignore": return IGN
        else: return Sym(obj)
    if type(obj) == type([]):
        return parse_json_array(obj)
    return obj

def parse_json_array(arr): 
    try:
        i = arr.index("#rest")
        front = arr[:i]
        return array_to_list(map(parse_json_value, front), parse_json_value(arr[i + 1]))
    except ValueError:
        return array_to_list(map(parse_json_value, arr))

# PyNI
class PyFun(object):
    def __init__(self, pyfun):
        if not hasattr(pyfun, '__call__'): fail('no fun')
        self.pyfun = pyfun
    def wat_combine(self, e, k, f, o):
        return self.pyfun(*list_to_array(o))

def pywrap(pyfun): return wrap(PyFun(pyfun))
def py_unop(op):
    def f(a): return eval(str(op) + str(a))
    return pywrap(f)
def py_binop(op):
    def f(a,b): return eval(str(a) + str(op) + str(b))
    return pywrap(f)
def py_invoke(obj, method_name, *args):
    return getattr(obj, method_name)(*args)
def py_callback(cmb):
    return lambda *args: combine(make_env(), None, None, cmb, array_to_list(args))
def setElement(obj, i, v): obj[i] = v

# Primitives
primitives = ["begin",
# Core
# Fexprs
         ["def", "--vau", __Vau()],
         ["def", "eval", wrap(Eval())],
         ["def", "make-environment", pywrap(make_env)],
         ["def", "wrap", pywrap(wrap)],
         ["def", "unwrap", pywrap(unwrap)],
# Values
         ["def", "cons", pywrap(cons)],
         ["def", "cons?", pywrap(lambda obj: type(obj) == type(Cons(None,None)))],
         ["def", "nil?", pywrap(lambda obj: obj is NIL)],
         ["def", "symbol?", pywrap(lambda obj: type(obj) == type(Sym('symbol')))],
         ["def", "symbol-name", pywrap(sym_name)],
# First-order Control
         ["def", "if", If()],
         ["def", "--loop", __Loop()],
         ["def", "throw", pywrap(fail)],
         ["def", "--catch", wrap(__Catch())],
         ["def", "finally", Finally()],
# Delimited Control
         ["def", "--push-prompt", wrap(__PushPrompt())],
         ["def", "--take-subcont", wrap(__TakeSubcont())],
         ["def", "--push-subcont", wrap(__PushSubcont())],
# Dynamically-scoped Variables
         ["def", "dnew", wrap(DNew())],
         ["def", "--dlet", wrap(__DLet())],
         ["def", "dref", wrap(DRef())],
# Python Interface
         ["def", "py-wrap", pywrap(pywrap)],
         ["def", "py-unop", pywrap(py_unop)],
         ["def", "py-binop", pywrap(py_binop)],
         ["def", "py-element", pywrap(lambda obj, i: obj[i])],
         ["def", "py-set-element", pywrap(setElement)],
         ["def", "py-invoke", pywrap(py_invoke)],
         ["def", "py-callback", pywrap(py_callback)],
         ["def", "list-to-array", pywrap(list_to_array)],
# Optimization
         ["def", "list*", pywrap(list_star)],

# Primitives
         ["def", "quote", ["--vau", ["x"], "#ignore", "x"]],
         ["def", "list", ["wrap", ["--vau", "arglist", "#ignore", "arglist"]]],
         ["def", "string", ["--vau", ["sym"], "#ignore", ["symbol-name", "sym"]]],

         ["def", "make-macro-expander",
          ["wrap",
           ["--vau", ["expander"], "#ignore",
            ["--vau", "operands", "env",
             ["eval", ["eval", ["cons", "expander", "operands"], ["make-environment"]], "env"]]]]],

         ["def", "vau",
          ["make-macro-expander",
           ["--vau", ["params", "env-param", "#rest", "body"], "#ignore",
            ["list", "--vau", "params", "env-param", ["cons", "begin", "body"]]]]],

         ["def", "macro",
          ["make-macro-expander",
           ["vau", ["params", "#rest", "body"], "#ignore",
            ["list", "make-macro-expander", ["list*", "vau", "params", "#ignore", "body"]]]]],

         ["def", "lambda",
          ["macro", ["params", "#rest", "body"],
           ["list", "wrap", ["list*", "vau", "params", "#ignore", "body"]]]],
         ["def", "loop",
          ["macro", "body",
           ["list", "--loop", ["list*", "begin", "body"]]]],
         ["def", "catch",
          ["macro", ["protected", "handler"],
           ["list", "--catch", ["list", "lambda", [], "protected"], "handler"]]],

         ["def", "push-prompt",
          ["macro", ["prompt", "#rest", "body"],
           ["list", "--push-prompt", "prompt", ["list*", "lambda", [], "body"]]]],
         ["def", "take-subcont",
          ["macro", ["prompt", "k", "#rest", "body"],
           ["list", "--take-subcont", "prompt", ["list*", "lambda", ["list", "k"], "body"]]]],
         ["def", "push-subcont",
          ["macro", ["k", "#rest", "body"],
           ["list", "--push-subcont", "k", ["list*", "lambda", [], "body"]]]],

# Python
         ["def", "array", ["lambda", "args", ["list-to-array", "args"]]],

         ["def", "define-py-unop",
          ["macro", ["op"],
           ["list", "def", "op", ["list", "py-unop", ["list", "string", "op"]]]]],

         ["define-py-unop", "not"],
         ["define-py-unop", "type"],
         ["define-py-unop", "~"],

         ["def", "define-py-binop",
          ["macro", ["op"],
           ["list", "def", "op", ["list", "py-binop", ["list", "string", "op"]]]]],

         ["define-py-binop", "!="],
         ["define-py-binop", "!=="],
         ["define-py-binop", "%"],
         ["define-py-binop", "&"],
         ["define-py-binop", "&&"],
         ["define-py-binop", "*"],
         ["define-py-binop", "+"],
         ["define-py-binop", "-"],
         ["define-py-binop", "/"],
         ["define-py-binop", "<"],
         ["define-py-binop", "<<"],
         ["define-py-binop", "<="],
         ["define-py-binop", "=="],
         ["define-py-binop", "==="],
         ["define-py-binop", ">"],
         ["define-py-binop", ">>"],
         ["define-py-binop", ">>>"],
         ["define-py-binop", "^"],
         ["define-py-binop", "in"],
         ["define-py-binop", "instanceof"],
         ["define-py-binop", "|"],
         ["define-py-binop", "or"],

         ["def", ".",
          ["macro", ["field", "obj"],
           ["list", "py-element", "obj", ["list", "string", "field"]]]],

         ["def", "#",
          ["macro", ["method", "obj", "#rest", "args"],
           ["list*", "py-invoke", "obj", ["list", "string", "method"], "args"]]],
        ]
# Init 
environment = make_env()
bind(environment, Sym("def"), Def())
bind(environment, Sym("begin"), Begin())
# API
def run(x): return evaluate(environment, None, None, parse_json_value(x))
run(primitives)

if __name__ == '__main__':
    # test
    assert 1000 == run(['begin',['def','x',10],['*', 'x', ['*','x','x']]])
