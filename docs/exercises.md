---
layout: default
title: "Exercises"
author: "Community"
---

To get a new copy of the exercises, run the following commands in your terminal:

```
leanproject get lftcm2020
cp -r lftcm2020/src/exercises_sources/ lftcm2020/src/my_exercises
code lftcm2020
```

To update your exercise files, run the following commands:

```
cd /path/to/lftcm2020
git pull
leanproject get-mathlib-cache
```

Don't forget to copy the updated files to `src/my_exercises`.
