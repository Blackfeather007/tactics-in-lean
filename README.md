# tactics-in-lean

This repository stores exercises for the Lean seminar held in WestLake University, 2025.1.6-2025.1.24. It also serves as the tutorial for basic tactics in Lean 4.

To use this project, first clone it to your local:

```bash
git clone https://github.com/Blackfeather007/tactics-in-lean.git
```

Then build the project:

```bash
lake exe cache get
lake build
```

This project uses a fixed revision of Mathlib, which is `v4.14.0`. Run `lake update` won't change the `lake-manifest.json`. If you want to update the dependencies, please modify the `lakefile.lean`.


# Contribution Guide

For contributers of this project, please **DON'T COMMIT TO THE MAIN BRANCH DIRECTLY**. You should create your own branch and then open a pull request when ready. The pull request needs at least 1 reviewer.

As a quick reference, if you are a new contributer, first follow the instructions above to build the project. Then run:

```bash
git checkout -b $(Your branch name)
```

This will create a new branch in your local repository. **Note that your local branch won't be on remote until you publish it**. You should be on your branch after running the command. Make your commits on your branch only.

To push your branch to the remote, run:

```bash
git push origin $(Your branch name)
```

Note that you should run that command when you are on your branch locally. `origin` here represents the remote repository.

You can open a pull request following the GitHub's guide. After your branch merged into `main`, the easiest way to start annother round is delete your local branch and remote branch and create a new one from `main`. If you are an experienced git user, you can still use the old branch, but make sure your remote branch is up to date with `main` after doing some cleaning.

For git freshmen, starting from a new branch is recommended.