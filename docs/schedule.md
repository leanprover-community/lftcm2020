---
layout: default
title: "Schedule"
author: "Community"
---

The workshop will take place from **Monday 13th** through **Friday 17th July 2020**.

All times mentioned below are in **central European time** (CEST, UTC+2:00).

The virtual “common room” for this workshop is the
[**dedicated Zulip stream**](https://leanprover.zulipchat.com/#narrow/stream/238830-Lean-for.20the.20curious.20mathematician.202020).
In this stream we will post announcements, answer questions, and host any further discussion.

Most of the schedule below forms the *beginner track* of the workshop.
Intermediate users can work on pair programming with more advanced
users at any time, using the Zulip stream for coordination.

### Zoom sessions

Each session will start with a short presentation that either will have
been pre-recorded or will be live-recorded and available here during and
after the session.
Then it will move to an exercises session using online chat and
screen-sharing.

Please download and import the following iCalendar (.ics) files to your calendar system:
[Zoom schedule](https://vu-live.zoom.us/meeting/tJEpd-uopj4jGtRLTcJg_Y9FR5KHpW94me9h/ics?icsToken=98tyKuCtqjsoGtyQuRmHRowMBoiga_TxiCVEjbdvsCvmKSdsW1rQBLdpGqJISYzd)

Join Zoom Meeting: [https://vu-live.zoom.us/j/95402085900](https://vu-live.zoom.us/j/95402085900)

We will share the password in the Zulip stream mentioned above.

### Monday:

The goal of this first day is to make sure that all participants have
Lean and its supporting tools installed, and to start proving things
without knowing anything about foundations or theory building,
using the [Natural Number Game](http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/).

In parallel during the afternoon, intermediate users will have the
opportunity to learn about Lean's meta-programming framework, which allows
to automate some proofs.

Time | Activity | Speaker
---- | -------- | -------
07:00 -- 12:00 | Tech support ([installing Lean, using git + GitHub](https://www.youtube.com/playlist?list=PLlF-CfQhukNnxF1S22cNGKyfOrd380NUv)) |
13:00 -- 13:30 | [Welcome](https://www.youtube.com/watch?v=8mVOIGW5US4) + [1st Lean proof](https://www.youtube.com/watch?v=b59fpAJ8Mfs)  | Scott Morrison
13:30 -- 18:00 | [Natural number game (demo and exercises)](https://www.youtube.com/watch?v=9V1Xo1n_3Qw)                                 | Kevin Buzzard
13:30 -- 18:00 | [Meta-programming and tactic writing](https://www.youtube.com/playlist?list=PLlF-CfQhukNnq2kDCw2P_vI5AfXN7egP2)         | Rob Lewis


### Tuesday:

This second day focuses on basic proving techniques and manipulating elementary
objects. It will mostly rely on the
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
tutorial. We will cover most of the content of the tutorial and help people
doing the exercises.

Time | Activity | Speaker
---- | -------- | -------
10:00 -- 12:00 | [Mathematics in Lean: basics](https://www.youtube.com/watch?v=lw8EfTmWzRU&list=PLlF-CfQhukNlxexiNJErGJd2dte_J1t1N&index=5&t=443s) [(slides)](https://www.imo.universite-paris-saclay.fr/~pmassot/basics.pdf)              | Patrick Massot
13:00 -- 15:00 | [Mathematics in Lean: logic](https://www.youtube.com/watch?v=WGwKefZ8KFo)               | Jeremy Avigad
15:00 -- 16:30 | [Dealing with numbers: ℕ, ℤ, ℚ, ℝ, ℂ](https://www.youtube.com/watch?v=iEs2U_kzYy4)      | Rob Lewis
16:30 -- 18:00 | [Dealing with sets and operations on them](https://www.youtube.com/watch?v=qlJrCtYiEkI) | Jeremy Avigad

### Wednesday:

This third day focuses on *theory building*. This includes defining
mathematical structures (such as groups, rings, topological spaces...)
and their relations as well as proving enough basic lemmas to make them
usable.
All the examples that will be discussed are already
[known to Lean](https://leanprover-community.github.io/mathlib-overview.html),
but we will explain how build them from scratch.

Time | Activity | Speaker
---- | -------- | -------
10:00 -- 12:00 | Structures and classes [(video 1)](https://www.youtube.com/watch?v=xYenPIeX6MY) [(video 2)](https://www.youtube.com/watch?v=1W_fyjaaY0M)           | Floris van Doorn
13:00 -- 15:00 | [Rebuilding an algebraic hierarchy](https://www.youtube.com/watch?v=ATlAQPAtiTY)    | Kevin Buzzard
15:00 -- 17:00 | [Rebuilding a topological hierarchy](https://www.youtube.com/watch?v=RTfjSlwbKjQ)   | Alex J. Best


### Thursday:

This is the first of two days devoted to specific areas of mathlib,
Lean's mathematical library.
Here we won't rebuild definitions, but rather learn how built things can
be used, mostly by reproving lemmas that are already in mathlib.

Time | Activity | Speaker
---- | -------- | -------
10:00 -- 11:00 | [“Order”, including Galois connections](https://www.youtube.com/watch?v=vsnB7W9nODI)  | Kevin Buzzard
11:00 -- 12:00 | [“Groups, rings and fields”](https://www.youtube.com/watch?v=SdXvUU75cDA)             | Johan Commelin
13:00 -- 15:00 | [“Linear algebra”](https://www.youtube.com/watch?v=EnZvGCU_jpc)                       | Anne Baanen
15:00 -- 18:00 | [“Category theory”](https://www.youtube.com/watch?v=1NUc-ZNC_2s)                      | Scott Morrison


### Friday:

This will be similar to Thursday, but focusing on topology, analysis,
and differential geometry.

Time | Activity | Speaker
---- | -------- | -------
10:00 -- 12:00 | [“Topology”, including filters](https://youtu.be/hhOPRaR3tx0) [(slides)](https://www.imo.universite-paris-saclay.fr/~pmassot/topology.pdf)        | Patrick Massot
13:00 -- 15:30 | [“Calculus and integration”](https://youtu.be/p8Etfv1_VqQ)             | Yury Kudryashov
15:30 -- 18:00 | [“Differential geometry”](https://youtu.be/1xXRQmhldFs)                | Sébastien Gouëzel and Heather Macbeth
