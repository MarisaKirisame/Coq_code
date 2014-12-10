Write a dependently typed interpreter for a simple programming language
with ML-style pattern-matching, using one of the encodings of heterogeneous lists
to represent the different branches of a case expression. 
(There are other ways to represent the same thing, but the point of this exercise
is to practice using those heterogeneous list types.)
The object language is defined informally by this grammar:
t ::= bool | t + t
p ::= x | b | inl p | inr p
e ::= x | b | inl e | inr e | case e of [ p ⇒ e ]* | ⇒ e
The non-terminal x stands for a variable, and b stands for a boolean constant.
The production for case expressions means that a pattern-match
includes zero or more pairs of patterns and expressions, 
along with a default case.
Your interpreter should be implemented in the style demonstrated in this chapter.
That is, your definition of expressions should use dependent types and
de Bruijn indices to combine syntax and typing rules,
such that the type of an expression tells the types of variables that are in scope.
You should implement a simple recursive function translating types t to Set,
and your interpreter should produce values in the image of this translation.