# verify-todec
Formal check of Rafaello Guilietti's paper "Rendering doubles in Java"

This is an attempt to review mathematics behind contrubution to OpenJDK authored by Rafaello Guilietti.

Rafaello Guilietti has offered his code [1] to fix the problems described in the longstanding issue [2].
He also contributed the content of the CSR which I filed [3].
There are some pertinent posts to core-libs-dev in March [4] and April [5] as well.
In one of these the contributor posted a link to a background paper on the work [6].

In this repository I try to formally check his paper using ACL2 proof checker.
Definitions and theorems from Section N of the pape are in file acl2/sectionN.lisp .

[1] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-April/052696.html
[2] https://bugs.openjdk.java.net/browse/JDK-4511638
[3] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-May/052934.html
[4] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-March/052355.html
[5] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-April/thread.html
[6] https://9b7022c5f9.files.wordpress.com/2018/04/todec.pdf
[7] http://www.cs.utexas.edu/~moore/acl2/
