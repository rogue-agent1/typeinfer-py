#!/usr/bin/env python3
"""Hindley-Milner type inference with let-polymorphism."""
import sys

_counter = 0
def fresh():
    global _counter; _counter += 1; return TVar(f"t{_counter}")

class Type: pass
class TInt(Type):
    def __repr__(self): return "Int"
class TBool(Type):
    def __repr__(self): return "Bool"
class TVar(Type):
    def __init__(self, name): self.name = name
    def __repr__(self): return self.name
    def __eq__(self, o): return isinstance(o, TVar) and self.name == o.name
    def __hash__(self): return hash(self.name)
class TFun(Type):
    def __init__(self, arg, ret): self.arg, self.ret = arg, ret
    def __repr__(self): return f"({self.arg} -> {self.ret})"

def apply_sub(s, t):
    if isinstance(t, TVar): return s.get(t.name, t)
    if isinstance(t, TFun): return TFun(apply_sub(s, t.arg), apply_sub(s, t.ret))
    return t

def compose(s1, s2):
    r = {k: apply_sub(s1, v) for k, v in s2.items()}
    r.update(s1)
    return r

def occurs(name, t):
    if isinstance(t, TVar): return t.name == name
    if isinstance(t, TFun): return occurs(name, t.arg) or occurs(name, t.ret)
    return False

def unify(t1, t2):
    t1, t2 = apply_sub({}, t1), apply_sub({}, t2)
    if isinstance(t1, TInt) and isinstance(t2, TInt): return {}
    if isinstance(t1, TBool) and isinstance(t2, TBool): return {}
    if isinstance(t1, TVar):
        if t1 == t2: return {}
        if occurs(t1.name, t2): raise TypeError(f"Infinite type: {t1} in {t2}")
        return {t1.name: t2}
    if isinstance(t2, TVar): return unify(t2, t1)
    if isinstance(t1, TFun) and isinstance(t2, TFun):
        s1 = unify(t1.arg, t2.arg)
        s2 = unify(apply_sub(s1, t1.ret), apply_sub(s1, t2.ret))
        return compose(s2, s1)
    raise TypeError(f"Cannot unify {t1} with {t2}")

class Expr: pass
class EInt(Expr):
    def __init__(self, v): self.v = v
class EBool(Expr):
    def __init__(self, v): self.v = v
class EVar(Expr):
    def __init__(self, name): self.name = name
class ELam(Expr):
    def __init__(self, param, body): self.param, self.body = param, body
class EApp(Expr):
    def __init__(self, fn, arg): self.fn, self.arg = fn, arg
class ELet(Expr):
    def __init__(self, name, val, body): self.name, self.val, self.body = name, val, body

def infer(expr, env):
    if isinstance(expr, EInt): return {}, TInt()
    if isinstance(expr, EBool): return {}, TBool()
    if isinstance(expr, EVar):
        if expr.name not in env: raise TypeError(f"Unbound: {expr.name}")
        return {}, env[expr.name]()
    if isinstance(expr, ELam):
        tv = fresh()
        new_env = {**env, expr.param: lambda t=tv: t}
        s, t = infer(expr.body, new_env)
        return s, TFun(apply_sub(s, tv), t)
    if isinstance(expr, EApp):
        s1, t1 = infer(expr.fn, env)
        env2 = {k: (lambda f=v, s=s1: apply_sub(s, f())) for k, v in env.items()}
        s2, t2 = infer(expr.arg, env2)
        tv = fresh()
        s3 = unify(apply_sub(s2, t1), TFun(t2, tv))
        return compose(s3, compose(s2, s1)), apply_sub(s3, tv)
    if isinstance(expr, ELet):
        s1, t1 = infer(expr.val, env)
        env2 = {k: (lambda f=v, s=s1: apply_sub(s, f())) for k, v in env.items()}
        env2[expr.name] = lambda t=t1, s=s1: apply_sub(s, t)
        s2, t2 = infer(expr.body, env2)
        return compose(s2, s1), t2

def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--test":
        global _counter; _counter = 0
        # int literal
        _, t = infer(EInt(42), {})
        assert isinstance(t, TInt)
        # identity function
        _counter = 0
        _, t = infer(ELam("x", EVar("x")), {})
        assert isinstance(t, TFun)
        # application
        _counter = 0
        _, t = infer(EApp(ELam("x", EVar("x")), EInt(5)), {})
        assert isinstance(t, TInt), f"Got {t}"
        # let
        _counter = 0
        _, t = infer(ELet("id", ELam("x", EVar("x")), EApp(EVar("id"), EInt(3))), {})
        assert isinstance(t, TInt)
        print("All tests passed!")
    else:
        global _counter; _counter = 0
        _, t = infer(ELam("f", ELam("x", EApp(EVar("f"), EVar("x")))), {})
        print(f"λf. λx. f x : {t}")

if __name__ == "__main__":
    main()
