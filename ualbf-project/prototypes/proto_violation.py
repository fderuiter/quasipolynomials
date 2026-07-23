# A prototype python file with style/type violations
import os, sys

def bad_prototype( x,y ):
    bad_var = "a" * 200
    print(undefined_proto_variable)
    x: int = "not an int"
    return x

bad_prototype(1, 2)
