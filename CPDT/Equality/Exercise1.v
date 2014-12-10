1. Implement and prove correct a substitution function for simply typed lambda calculus.
In particular:
(a) Dene a datatype type of lambda types, including just booleans and function
types.
(b) Dene a type family exp : list type → type → Type of lambda expressions,
including boolean constants, variables, and function application and abstraction.
(c) Implement a denitional interpreter for exp s, by way of a recursive function over
expressions and substitutions for free variables, like in the related example from
the last chapter.
(d) Implement a function subst : ∀ t' ts t , exp ( t' :: ts ) t → exp ts t' → exp ts
t . The type of the rst expression indicates that its most recently bound free
variable has type t' . The second expression also has type t' , and the job of subst
is to substitute the second expression for every occurrence of the rst variable
of the rst expression.
(e) Prove that subst preserves program meanings. That is, prove
∀ t' ts t ( e : exp ( t' :: ts ) t ) ( e' : exp ts t' ) ( s : hlist typeDenote ts ),
expDenote ( subst e e' ) s = expDenote e ( expDenote e' s ::: s )
where ::: is an inx operator for heterogeneous cons that is dened in the book's
DepList module.
The material presented up to this point should be sucient to enable a good solution
of this exercise, with enough ingenuity. If you get stuck, it may be helpful to use the
following structure. None of these elements need to appear in your solution, but we
can at least guarantee that there is a reasonable solution based on them.
8(a) The DepList module will be useful. You can get the standard dependent list
denitions there, instead of copying-and-pasting from the last chapter. It is worth
reading the source for that module over, since it denes some new helpful functions
and notations that we did not use last chapter.
(b) Dene a recursive function liftVar : ∀ ts1 ts2 t t' , member t ( ts1 ++ ts2 ) →
member t ( ts1 ++ t' :: ts2 ). This function should lift a de Bruijn variable so
that its type refers to a new variable inserted somewhere in the index list.
(c) Dene a recursive function lift' : ∀ ts t ( e : exp ts t ) ts1 ts2 t' , ts = ts1 ++
ts2 → exp ( ts1 ++ t' :: ts2 ) t which performs a similar lifting on an exp . The
convoluted type is to get around restrictions on match annotations. We delay
realizing that the rst index of e is built with list concatenation until after a
dependent match , and the new explicit proof argument must be used to cast some
terms that come up in the match body.
(d) Dene a function lift : ∀ ts t t' , exp ts t → exp ( t' :: ts ) t , which handles simpler
top-level lifts. This should be an easy one-liner based on lift' .
(e) Dene a recursive function substVar : ∀ ts1 ts2 t t' , member t ( ts1 ++ t' :: ts2 )
→ ( t' = t ) + member t ( ts1 ++ ts2 ). This function is the workhorse behind
substitution applied to a variable. It returns inl to indicate that the variable we
pass to it is the variable that we are substituting for, and it returns inr to indicate
that the variable we are examining is not the one we are substituting for. In the
rst case, we get a proof that the necessary typing relationship holds, and, in the
second case, we get the original variable modied to reect the removal of the
substitutee from the typing context.
(f) Dene a recursive function subst' : ∀ ts t ( e : exp ts t ) ts1 t' ts2 , ts = ts1 ++
t' :: ts2 → exp ( ts1 ++ ts2 ) t' → exp ( ts1 ++ ts2 ) t . This is the workhorse
of substitution in expressions, employing the same proof-passing trick as for lift' .
You will probably want to use lift somewhere in the denition of subst' .
(g) Now subst should be a one-liner, dened in terms of subst' .
(h) Prove a correctness theorem for each auxiliary function, leading up to the proof
of subst correctness.
(i) All of the reasoning about equality proofs in these theorems follows a regular
pattern. If you have an equality proof that you want to replace with eq re
somehow, run generalize on that proof variable. Your goal is to get to the
point where you can rewrite with the original proof to change the type of the
generalized version. To avoid type errors (the infamous second-order unication
failure messages), it will be helpful to run generalize on other pieces of the
proof context that mention the equality's lefthand side. You might also want to
use generalize dependent , which generalizes not just one variable but also all
variables whose types depend on it. generalize dependent has the sometimes-
helpful property of removing from the context all variables that it generalizes.
9Once you do manage the mind-bending trick of using the equality proof to rewrite
its own type, you will be able to rewrite with UIP re .
(j) The ext eq axiom from the end of this chapter is available in the Coq standard
library as functional extensionality in module FunctionalExtensionality , and you
will probably want to use it in the lift' and subst' correctness proofs.
(k) The change tactic should come in handy in the proofs about lift and subst ,
where you want to introduce extraneous list concatenations with nil to match
the forms of earlier theorems.
(l) Be careful about destruct ing a term too early. You can use generalize on
proof terms to bring into the proof context any important propositions about the
term. Then, when you destruct the term, it is updated in the extra propositions,
too. The case eq tactic is another alternative to this approach, based on saving
an equality between the original term and its new form.