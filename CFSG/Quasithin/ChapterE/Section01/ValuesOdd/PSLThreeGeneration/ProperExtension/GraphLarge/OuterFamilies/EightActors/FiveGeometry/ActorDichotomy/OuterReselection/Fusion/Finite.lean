module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.VecNotation

/-!
# Finite coordinates for the fixed PSL₃(5) Sylow

Coordinates encode x^i y^j w^b t^c, with the torus exponents modulo four,
the signed transposition w, and inverse transpose t. The transposition acts
on exponents by (i,j) ↦ (i,-i-j); inverse transpose negates them.
The eight explicit lists retain every element of each actor.
`Fusion.Carrier` connects these arithmetic definitions to the literal model.

Source: the fixed-Sylow calculation supporting Aschbacher--Smith E.1.14(7),
printed p.214. The lists and witnesses were discovered by the saved GAP
`OuterReselection/FusionWitnesses.g`; every fact below is kernel checked.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection.Fusion

abbrev D := ZMod 4 × ZMod 4
abbrev L := D × Bool
abbrev C := L × Bool

@[expose] def twist (c : Bool) (d : D) : D := if c then -d else d
@[expose] def sw (b : Bool) (d : D) : D := if b then (d.1, -d.1-d.2) else d
@[expose] def cmul (a b : C) : C :=
  ((a.1.1 + sw a.1.2 (twist a.2 b.1.1), a.1.2 ^^ b.1.2), a.2 ^^ b.2)
@[expose] def ce : C := (((0,0),false),false)

/-- The eight complete coordinate sets, in the saved diagnostic's order. -/
@[expose] def codes : Fin 8 → Finset C :=
  ![{(((0,0),false),false), (((0,2),false),false), (((0,2),true),false), (((0,0),true),false), (((2,1),false),true), (((2,3),false),true), (((2,1),true),true), (((2,3),true),true)},
    {(((0,0),false),false), (((0,2),false),false), (((0,3),true),false), (((0,1),true),false), (((0,3),false),true), (((0,1),false),true), (((0,2),true),true), (((0,0),true),true)},
    {(((0,0),false),false), (((2,2),false),false), (((2,0),false),false), (((0,2),false),false), (((0,3),false),true), (((2,1),false),true), (((2,3),false),true), (((0,1),false),true)},
    {(((0,0),false),false), (((2,2),false),false), (((2,0),false),false), (((0,2),false),false), (((3,3),false),true), (((1,1),false),true), (((1,3),false),true), (((3,1),false),true)},
    {(((0,0),false),false), (((2,2),false),false), (((2,0),false),false), (((0,2),false),false), (((1,0),false),true), (((3,2),false),true), (((3,0),false),true), (((1,2),false),true)},
    {(((0,0),false),false), (((2,2),false),false), (((2,0),false),false), (((0,2),false),false), (((0,0),false),true), (((2,2),false),true), (((2,0),false),true), (((0,2),false),true)},
    {(((0,0),false),false), (((0,2),false),false), (((0,2),true),false), (((0,0),true),false), (((0,0),false),true), (((0,2),false),true), (((0,2),true),true), (((0,0),true),true)},
    {(((0,0),false),false), (((0,2),false),false), (((0,3),true),false), (((0,1),true),false), (((2,2),false),true), (((2,0),false),true), (((2,1),true),true), (((2,3),true),true)}]

theorem codes_card : ∀ i, (codes i).card = 8 := by decide +kernel
theorem codes_one : ∀ i, ce ∈ codes i := by decide +kernel
theorem codes_sq : ∀ i a, a ∈ codes i → cmul a a = ce := by decide +kernel
theorem codes_mul : ∀ i a, a ∈ codes i → ∀ b, b ∈ codes i →
    cmul a b ∈ codes i := by decide +kernel

/-- A purely finite census contract. It asserts coverage of whole sets of eight
commuting involutions, with no assumed ambient conjugacy information. -/
@[expose] def Census : Prop :=
  ∀ s : Finset C, s.card = 8 → (∀ a ∈ s, cmul a a = ce) →
    (∀ a ∈ s, ∀ b ∈ s, cmul a b = cmul b a) → ∃ i, s = codes i

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection.Fusion
