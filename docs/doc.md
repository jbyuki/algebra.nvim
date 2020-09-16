algebra.nvim
============

algebra.nvim is a plugin for neovim which allows to manipulate,
simplify and evaluate symbolic expressions. 

Default keybindings:
* <kdb>F2</kbd> : Simplify the current expression
* <kdb>F3</kbd> : Evaluate the current expression
* <kdb>F4</kbd> : Output the current expression as LaTex
* <kdb>F5</kbd> : Show the symbol table
### `parenthesis`
Used to prioritize expression or used to evaluate a function.
Examples:
```
(1+x)^2
cos(10)
```

### `numbers`
Numbers are all represented as floating points.
Examples:
```
2
10.3
```

### `symbols`
Symbols are reprensented as `[alphanumeric | _]`
Examples:
```
F
_1
d1
```

### `constants`
The following constants are defined:
* `pi` : 3.141592...
* `e` : 2.7182...

Examples
```
pi
```
### `Addition`
Examples:
```
1 + 10
1 + x
y + x
```

### `Prefix negative`
Examples:
```
-10
-2.71
```

### `Substraction`
Examples:
```
1-0
x-1
```

### `Multiplication`
Examples:
```
10*(x+1)
8*x
```

### `Divison`
Examples:
```
10/8
x/y
```

### `Function call`
The following functions are built-in:
* `sin(x)`: sine in radians
* `cos(x)`: cosine in radians
* `tan(x)`: tangent in radians
* `sqrt(x)`: square root
* `asin(x)`: inverse sine in radians
* `acos(x)`: inverse cosine in radians
* `atan(x)`: inverse tangent in radians
* `ln(x)`: natural logarithm or log to the base e
* `log(x)`: logarithm in the base 10
* `exp(x)`: exponential or `f(x) = e^x`
* `atan2(x,y)`: two argument variant of tangent
* `abs(x)`: absolute value

* `sind(x)`: sine in degrees
* `cosd(x)`: cosine in degrees
* `tand(x)`: tangent in degress
* `asind(x)`: inverse sine in degrees
* `acosd(x)`: inverse cosine in degrees
* `atand(x)`: inverse tangent in degress

Examples:
```
cosd(90)
sin(9)
```

Additionally user defined functions can be called.
A function is defined simplify with an assignement such as:
```
A := x^2
```
The interpreter will automatically infer paramters to the function
when the symbol is **not** defined. When the arguments list is infered,
it is sorted lexically. For example, this function will have
as arguments list `B(x,y)`.
```
B := y+x
```
The user defined function can then be called using the familiar function
call syntax.
```
B(10, 1)
```


### `exponentation`
Examples:
```
2^5
(x+1)^2
```

### `Vector, matrix`
The expression is delimited by `[]`.
Rows are delimited by `;`.
Cells in a row are delimited by `,`.
Examples:
```
[1,2]
[1;7]
[1,2;3,4]
```

### `grad(x)`
Compute the gradient in x, y and z
Arguments:
* `x`: any expression
```
grad(x^2+y*z)
A := x^2+z*y+y
grad(A)
```

### `div(x)`
Compute the divergence in x, y and z.
Arguments:
* `x`: matrix expression
```
A := [x*y;x;z]
div(A)
```

### `rot(x)`
Compute the rotational in x, y and z.
Arguments:
* `x`: 3 x 1 matrix expression 
```
A := [x*y;x;z]
rot(A)
```

### `laplace(x)`
Laplace operator in x, y and z.
Arguments:
* `x`: any expression
```
A := x^2+y^2+z^2
laplace(A)
```


### `det(x)`
Compute the determinant of a square matrix
Arguments:
* `x`: square matrix expression
```
A := [1,2;3,4]
det(A)
```


### `transpose(x)`
Transpose the matrix
Arguments:
* `x`: matrix expression
```
A := [1,2;3,4]
transpose(A)
```

### `dot(x,y)`
Compute the dot products of two column vectors.
Arguments:
* `x`: n x 1 matrix expression
* `y`: n x 1 matrix expression
```
A := [1;2]
B := [3;4]
dot(A, B)
```

### `cross(x,y)`
Compute the cross products of two column vectors.
Arguments:
* `x`: 3 x 1 matrix expression
* `y`: 3 x 1 matrix expression
```
A := [0;0;1]
B := [1;0;1]
cross(A, B)
```


