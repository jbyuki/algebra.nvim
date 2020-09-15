algebra.nvim
------------

Computer algebra system for Neovim.

Features include:
* basic arithmetic operations: +, -, \*, /,...
* parenthesis
* variables assignment
* common math functions: cos, sin, tan, sqrt, ...
* constants (pi)
* symbolic derivation
* matrices add/mul
* matrices operators: grad, div, rot,...
* functions
* LaTex output

Install
-------

Install using your favorite plugin manager. No additional dependencies

Usage
-----

* <kbd>F2</kbd>: simplify the current line
* <kbd>F3</kbd>: evaluate the current line
* <kbd>F5</kbd>: display the symbol table

Example
-------

```
x := 2
x + 4
(y-1)^2
[1,2;3,4]*[1,2;3,4]
[1,2;3,4]^5
F(x,y,z) = [x^2+y;z^2;x*y*z]
rot(F)
G(x,y,z) = x^2 + y*z + z^3
grad(G)
```
