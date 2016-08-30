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

Status
------

We don't even know yet for sure which language to use and with which proof
assistant to perform the core work of this study.

See also
--------

  * [The ECMAScript standard][1]
  * [Scheme specification][2]

[1]: http://www.ecma-international.org/publications/standards/Ecma-262.htm
[2]: http://www.r6rs.org/final/r6rs.pdf

<!-- vim: set spell: -->

