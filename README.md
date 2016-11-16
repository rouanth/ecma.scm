ecma.scm
========

Description
-----------

Most web browsers nowadays only support JavaScript for full-fledged front-end
web development.

This lack of freedom has led to emergence of a multitude of projects the goal
of which were to create compilers from some other languages into JavaScript.

However JavaScript is quite a complex language, and it's hard not to let errors
or slight compatibility bugs crawl into the compiler. As a result, some obscure
problems may arise from time to time. And it's a common fact that the
compiler-induced problems are the hardest to debug since programmers commonly
attribute the misbehavior of code to their own negligence.

Our goal is to create a compiler from some language to JavaScript and formally
prove that given a program in the source language, the results of its execution
and the execution of the JavaScript code it compiles into are identical.

Language choice
---------------

We've chosen the Algorithmic Language Scheme for our purpose.

The language is very simple to implement and reason about since it has few
constructs which are easy to reason about but at the same time extensible
enough to allow for representation of complex programming concepts such as
Object-Oriented Programming. These properties are really inherent to Lisp,
making it perfect for language research.

Scheme stands out among the dialects of Lisp as the language that's more
focused on being appealing to language researches as opposed to production
developers.

We shall use the R6RS variant of Scheme since it's the most modern one. There
exists a specification of R7RS, but it only describes a small language intended
primarily for language research. The latest revision of the large language
which, while being still relatively small in size, is comfortable programming
is R6RS. We believe that the large variant of Scheme is a nice trade-off
between usability and ease of formalization.

Status
------

We've chosen the language and are currently studying it to determine the ways
it can be represented in Coq.

See also
--------

  * [The ECMAScript standard][1]
  * [Scheme specification][2]
  * [Comprehensive list of existing translators of Lisps to JavaScript][3]

[1]: http://www.ecma-international.org/publications/standards/Ecma-262.htm
[2]: http://www.r6rs.org/final/r6rs.pdf
[3]: http://ceaude.twoticketsplease.de/js-lisps.html

<!-- vim: set spell: -->

