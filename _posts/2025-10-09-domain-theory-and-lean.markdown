---
layout: post
title:  "Formaising Domain Theory with Lean"
author: Anna Williams
date:   2025-10-09 13:15:00 +0000
tags: lean domain-theory
categories: proof-assistants
---

Over the summer I had a research project where I learnt some basic domain theory alongside formalising it in lean. It was a really good opportunity to get stuck into the subject, especially with my existing familiarity with proof assistants meaning that I could focus more on the learning side with domain theory. I also think that formalising mathematics is one of the best ways to understand a topic well. At the end of the project I wrote a paper (which is [here](/assets/papers/domains_lean.pdf)). I wanted to go a little more in depth on some of the decisions I made during formalisation that I felt didn't quite fit the scope of the paper, which was more aimed at people new to proof assistants. The codebase is [here](https://codeberg.org/awsloth/LeanDomainTheory).

## Subsets

To represent subsets we have to use a predicate, which tells us whether each given item is in the subset or not. If it is in the subset, we return `True` and if it isn't we return `False`. We can therefore define the notion of a subset on a given type `X` as follows, namely a function from `X` to `Prop` as we described above.

```lean
def Subset (X : Type) : Type :=
  X → Prop
```

## Elements of subsets or having key properties

Often in a definition or theorem we want items which belong to a certain subset or have a certain property. For example, when defining a directed set, we say that each pair of items in the subset has a least upper bound also in the subset. That is, a subset \\(A\\) is directed if

\\[
    \forall x, y \in A, \exists z \in A, x \sqsubseteq z \text{ and } y \sqsubseteq z.
\\]


At the start of the project I would write it like as follows, where `pred` was the predicate determining that any given item was in the subset.

```lean
pairwiseUB : ∀ x y : D, pred x → pred y → ∃ z : D, pred z → x ⊑ z ∧ y ⊑ z
```
This meant that the last section `x ⊑ z ∧ y ⊑ z`, reads well but all the preamble is kinda weird and finicky to read (every element in \\(D\\), such that it is also in this subset, ...). Throughout the project this became kind of annoying and I thought it looked quite ugly and unintuitive. I therefore decided to wrap up together the element in \\(D\\) and the proof it was that it satisfied the predicate into one.

```lean
def inAndProof (pred : Pred D) : Type :=
  Σ' a : D, pred a

pairwiseUB : ∀ x y : inAndProof pred, ∃ z : inAndProof pred, x.fst ⊑ z.fst ∧ y.fst ⊑ z.fst
```

I don't think the choice of name `inAndProof` was the best, but this is much cleaner. Once you get past the naming of things it becomes much clearer what is happening here and looks more natural. So the last step was to rename the wrapper `inAndProof` to `inSubset` and rename our predicate `pred` to be some subset `S`.

```lean
def inSubset (pred : Pred D) : Type :=
  Σ' a : D, pred a

pairwiseUB : ∀ x y : inSubset S, ∃ z : inSubset S, x.fst ⊑ z.fst ∧ y.fst ⊑ z.fst
```

I think this now looks much better and more readable to the mathematical eye now. My one problem is that of the last half - `x.fst ⊑ z.fst ∧ y.fst ⊑ z.fst`. I think this can be remedied, by redefining `⊑`, so that it automatically compares just the first elements of the pairs `x` and `y`, but this might get confusing and there is only so far we can go in the name of readability.

## The whole `lessThanLub` of it all

To express the notion of \\(a \ll b\\), we have to express that \\(b \sqsubseteq \bigsqcup D\\), for some directed set \\(D\\). As we are working in a dcpo and every directed set has a least upper bound, it would make sense that we can take this least upper bound and have this as a proposition. Annoyingly Lean has this thing called "proof irrelevance", which means that once you have an element of `∃ a, p a`, it removes all the data associated with it. This means that we can't simply take the item that is the least upper bound and work with that. Now I'm pretty sure I could do this in agda and it would be completely fine but we'll have to work around it. To do this we define a new property, that of being less than a least upper bound (well *the*, as they are unique in fact) as follows.

```lean
def lessThanLub (ds : isDirected p) (y : D) : Prop :=
    ∃ a : D, LeastUpperBound p a ds.fst ∧ y ⊑ a
```

This feels a little bit janky, but it's the best solution I could come up with for the moment (lmk if you have any better ideas!).

## Dcpo proofs

I think these were the biggest obstacle to my proofs, I wanted to prove these all constructively, but it turns out this is with the current representation. I haven't read Tom de Jong's paper on solving this because I haven't had time, but I would like to soon. This problem led to some pretty ugly code in the proof that the two item set is a dcpo, where I had to prove that any given subset was in \\(\{\{\}, \{\bot\}, \{\top\}, \{\top, \bot\}\}\\), so I had lots of different lemmas to show this. This wasn't difficult but takes up a significant amount of the file for something that feels like it should be pretty simple.
