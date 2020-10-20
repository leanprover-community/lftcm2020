# Lean for the Curious Mathematician 2020

This repository hosts the Lean demos and exercises from the meeting
[Lean for the Curious Mathematician](https://leanprover-community.github.io/lftcm2020/),
held virtually in July 2020.
Recordings of the tutorials at this meeting are
[available on YouTube](https://www.youtube.com/playlist?list=PLlF-CfQhukNlxexiNJErGJd2dte_J1t1N).

(The repository also hosts the meeting website, but you can ignore this.)

## Layout

In the `src` folder, you will find a number of subdirectories containing Lean files:

* `for_mathlib` contains some background material that you can ignore.
* `demos` contains some files that wre used during the category theory
  and linear algebra tutorials.
* `exercise_sources` contains exercises corresponding to each tutorial,
  organized by day.
* `hints` contains some helpful hints for these exercises.
* `solutions` contains completed exercises, if you're confused and want to peek.

## Getting started

We strongly recommend
[installing](https://leanprover-community.github.io/get_started.html#regular-install)
Lean with its supporting tool `leanproject`.
Then you can get this project and open it in VSCode by running:
```
leanproject get lftcm2020
cp -r lftcm2020/src/exercises_sources/ lftcm2020/src/my_exercises
code lftcm2020
```

We recommend the second line which copies the exercises to a new directory.
Otherwise, if you try to update this project, your exercise solutions
could be overwritten or create merge conflicts.
