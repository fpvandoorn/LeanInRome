# Sets and Functions

## Introduction
Sets are **primitive** objects when doing classical, old-school, pen-and-paper mathematics: there is no *definition* of what a set is, there are only *rules* about how these objects work, governing their behaviour under unions, intersections, etc. For Lean, sets are **no longer primitive objects**, but the same rules hold.


In the same vein, for Lean functions are **primitive** objects: there is no *definition* of what a function (between two "types") is, there are only *rules* about how these fundamental objects behave.

Concretely, that's all you need: one rarely (never?) uses that in set-theoretic language a function between $S$ and $T$ is really a subset of $S\times T$ satisfying some property.

+++ At the end of the day, everything is the same.
But in the morning, things seem different, and it takes a while to get used to them.
+++

## Sets

Mathematical objects that are normally represented by a set (like a group, a ring, a differentiable manifold, the set of prime numbers, a Riemann surface, the positive reals, etc...) are formalised in Lean as *types* endowed with some extra-structure.

Yet sometimes we really want to speak about *sets* as collections of elements and to play the usual games.

### Basic features

+++ Any set lives in a given type: it is a set of elements (*terms*) of a type:
```lean
(α : Type) (S : Set X)
```
expresses that α is any type and `S` is a set of elements/terms of the type α. On the other hand,
```lean
S : Set
```
does not mean "let `S` be a set": it means nothing and it is an error.
+++

+++ A set **coincides** with the property defining it

 Given a type α, a set `S` (of α) is a *function*
```lean
S : α → Prop
```
You can think of this function as being the characteristic function of $S$; indeed, the $\in$ symbol means that the value of `S` is `True`:
```lean
example (α : Type)(x : α) (S : Set α) : x ∈ S ↔ S x := rfl
```
You might think that $x \in S$ is the proposition that is true when $x$ belongs to $S$ and is false otherwise.
+++

+++ Sub(sub-sub-sub)sets are not treated as sets-inside-sets.
<br>

Let's think old-stylish for a moment:
+++ Given a set $S$, what is a subset $T$ of $S$ *for you*?
1. Another set such that $x\in T\Rightarrow x \in S$
1. A set of elements of $S$.
1. ... is there **any difference** whatsoever ?!

**Yes**: you can either stress the fact that it is a honest set satisfying some property; or the fact that it is a set whose "ambient space" is $S$. We take the first approach.

<!-- <br>
 -->
So, given two sets  `S T : Set α`, the property that `T` is a subset of `S` is an *implication*
```lean
def T ⊆ S := ∀ a, a ∈ T → a ∈ S
```
Let's see a live example!
+++

### Main constructions
+++ Intersection
```lean
def (S T : Set α) : S ∩ T := fun a => a ∈ S ∧ a ∈ T
```
+++

+++ Union
```lean
def (S T : Set α) : S ∪ T := fun a => a ∈ S ∨ a ∈ T
```
+++

+++ The empty set
This is the constant function `False : Prop` (and not `false : Bool`!)
```lean
def (∅ : Set α) := False
```
+++

+++ Set subtraction TODO
Given sets...

Let's see now an example combining subtraction and the empty set.
+++

+++ Indexed intersection and union
Instead of interscting and taking unions of *two* sets, we can allow fancier indexing sets (that will actually be **types**, *ça va sans dire*): for the intersection, for instance, we have
+++


## Functions

As said, functions **among types** are *primitives*, so we do not expect to find a definition for them. Still, we want to speak about functions among *sets*, and they will most likely be different gadgets, requiring a small change of perspective.

Let's inspect the following code:
```lean
example (α β : Type) (S : Set α) (f g : S → β) :
    f = g ↔ ∀ a : α, a ∈ S → f a = g a :=
```
+++ It *seems* to say that given two functions `f, g` whose domain is a set `s` of elements in `α`, they are equal if and only if they coincide on every element of the domain, yet...

```
application type mismatch
  f a
argument
  a
has type
  α : Type
but is expected to have type
  ↑s : Type
```

The above example shows that what really happens is that functions `f : α → β` can be *upgraded* to functions between sets. This reminds — for instance — the way that in "old-school, pen-and-paper, mathematics" a function $\varphi : X/\mathcal{R} \to Y$ on a quotient can be lifted to a function on $X$ by declaring that $\varphi(x)=\varphi(\overline{x})$: in both cases, we get something "natural" but it is safe to keep in mind that they are not really "the same thing".
+++

### Main constructions

Given a function `f : α → β` and sets `(S : Set α), (T : Set β)`, there are some constructions or properties we can analyze:

+++ The image of `S` through `f`, noted `f '' S`.
This is the *set* `f '' S : Set β` whose defining property is
```lean
∃ x, x ∈ S ∧ f x = a
```
+++

+++ The range of `f`, equivalent to `f '' univ`.
I write *equivalent* because the defining property is
```lean
range f := fun a => ∃ x, f x = a : β → Prop
```
Can you see why this is not the verbatim definition of `f '' univ`? If not, there is an exercise waiting...
+++

+++ The preimage of `T` through `f`, noted `f ⁻¹' T`.
This is
+++

+++ The function `f` is **injective on `s`**, denoted by `InjOn f s` if it is injective (a notion defined for functions **between types**) when restricted to `s`.
This is
+++