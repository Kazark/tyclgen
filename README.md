# tyclgen

## Type Class Generator for F\#

Ambitious, but not as good as it sounds. Basically I want a way to represent
a typeclass with instances and compile it to F# in such a way that though
higher kinded types and ad hoc polymorphism are not available in F# itself, the
results of compiling from a mini-language in which they are representable is
usable in F# to a significant degree, e.g. a `map` function will work on many
types, and yet have itself true abstract type signature expressed as fully as
possible, even if somewhat indirectly. This is implemented via milking
statically-resolved runtime parameters in F# for all they are worth. Or, you
might say, this is a horrible abuse of F#.

## Why this, you crackpot?

That's what I'm asking myself.

What captivated me when I first starting learning F# was the idea of making
illegal states unrepresentable. Or said in a more crash way, I loved the fact
that I got far fewer runtime exceptions than I had previously been used to, and
that I didn't have to account for nearly as many spurious "this should never
happen" cases. This line of thinking led me to Idris. Working too much in Idris
has made me irreparably think of software in terms of types. I have come to
love the composability, orthogonality, local reasoning, fast feedback cycle,
and everything else that is empowered by statically typed functional
programming. I continually want more. I keep asking myself, is this dogmatism?
I find that a year or two down the line, I often wish I had been more dogmatic.
We can so easily argue ourselves out of the rigor we ought to have in
programming.

My problems with expressing myself in F# slowly built over time. I came up with
many awful infix operators to represent `map`, `bind`, etc, for various types,
since I could only make them monomorphic. Finally, I started using statically
resolved type parameters, and was able to boil a lot of these down to single
operators.

The point at which this intensified though was when I started to realize that
if you write much code with lists, either/result, and pair, you quickly need
`traverse` a la Haskell's `Data.Traversable`. This becomes necessary even
before you have hit the point that you are writing truly pure functional code.
But now you have the fun of *n* `x` *m* implementations, since `traverse`
involves _two_ functors (one foldable at least, and the other applicative at
least). The shear length of the names required to express each monomorphic
implementation of traversable makes it painful to use, and the great table of
implementations necessary means that rarely do you actually have all the
instances you want implemented, and you have a lot of duplicated code, some of
which is nontrivial (traverse is moderately complex to implement for some pairs
of types), you never want to add new functor types...

So I tried to solve that, as much as I could, with SRTP. And then we had some
[code](https://github.com/Kazark/fsharp-srtp-broken) that [compiled and crashed
at runtime](https://github.com/Microsoft/visualfsharp/issues/4924)... the
opposite of everything I had been striving for.
I [found](https://github.com/Kazark/fsharp-srtp-broken/tree/feature-fixed) that
if I updated the rigor of what I was doing, I could get the bad code to not
compile, even without the F# compiler being fixed. However, so much boilerplate
was required to get the SRTP stuff working, I no longer trusted myself to write
it by hand (that had been a dicey endeavor before).

So I started writing a code generator. I thought, this is going from bad to
worse already, but I can't turn back from the drive towards making my F# code
as pure functional as I can, and I need traversable even if it's not that pure.
So I thought, I'll at least write the generator in F#.

But I couldn't stop seeing the problem in terms of dependent types. And thus,
you have hear, the incredible evil, that a man who knows comparatively little
about type theory and compilers, has written this. Whatever this is.

Look on, you developers, and despair. Round the decay of this little wreck,
boundless and bare, the lone and level boilerplate stretches far away.

