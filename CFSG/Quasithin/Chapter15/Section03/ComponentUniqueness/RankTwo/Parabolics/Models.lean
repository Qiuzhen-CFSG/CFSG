module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Definitions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Models

/-!
# The model alternatives in the final proof of 15.3.35

These are conclusion interfaces for the parabolic inspection on printed
p.1139. Every family carries a genuine model equivalence. The larger-field
list excludes the small derived groups and ties each parameter to its field.
The Borel is the normalizer of an actual Sylow two-subgroup inside L, then
mapped into the ambient group; it is not the ambient Sylow normalizer.

No model selection or Borel containment theorem is asserted here. Those
facts must be proved from 1.1.5(3)(a)--(c), the local configuration of
15.3.41 and the preceding action conclusions. The ambient group below is
I in the source, so normality of L is relative to I.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 1.1.5(3)
printed pp.501--502 and the final proof of 15.3.35, printed p.1139.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics

open Subgroup Theory.GroupTheory
open Candidates.ComponentStructure Chapter1.Section02.LocalModels

universe u

/-- The first three alternatives of 1.1.5(3), including the action clauses.
The automorphism must be identified with the actual action of z by the caller. -/
def CharacteristicTwoAction115 (L : Type u) [Group L] (α : MulAut L) : Prop :=
  (IsSimpleGroup L ∧ LieTypeTwoModel L ∧ α ∈ (MulAut.conj (G := L)).range) ∨
  (center L ≠ ⊥ ∧ center L = pCore 2 L ∧
    (ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4 ∨
      ClassificationModels.IsG2At (L ⧸ pCore 2 L) 4) ∧
    α ∈ (MulAut.conj (G := L)).range) ∨
  ∃ σ : Equiv.Perm (Fin 6), σ.IsSwap ∧ AlternatingAction α 6 σ

/-- The two binary linear possibilities on the first line of p.1139. -/
def SmallBinaryModel (D : Type u) [Group D] : Prop :=
  ClassicalGroup.IsPSL D 4 2 ∨ ClassicalGroup.IsPSL D 5 2

/-- Lie rank two over a binary field strictly larger than F₂.
For the Ree family the field order is 2^(2m+1), with m positive. -/
inductive LargerFieldRankTwoModel (D : Type u) [Group D] : Prop
  | linear (n : ℕ) (hn : 1 < n) (model : ClassicalGroup.IsPSL D 3 (2 ^ n))
  | symplectic (n : ℕ) (hn : 1 < n) (model : ClassicalGroup.IsPSp D 2 (2 ^ n))
  | g2 (n : ℕ) (hn : 1 < n) (model : ClassificationModels.IsG2At D (2 ^ n))
  | triality (n : ℕ) (hn : 1 < n)
      (model : Triality.Standard.IsTrialityGroupAt (2 ^ n) D)
  | ree (m : ℕ) (hm : 1 ≤ m) (model : IsReeF4At D m)

variable {G : Type*} [Group G]

/-- The actual Borel of L over S ∩ L, with its Sylow marking. -/
def BorelOverSylow (L S B : Subgroup G) : Prop :=
  ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = S ⊓ L ∧
    B = (normalizer (P : Set L)).map L.subtype

/-- The first parabolic reduction on p.1139. The component image is formed
in the genuine centralizer quotient, while the Borel is in the original L. -/
def ParabolicAlternatives (L Yplus S : Subgroup G) [L.Normal] : Prop :=
  SmallBinaryModel (centralizerQuotientComponent L) ∨
  (LargerFieldRankTwoModel (centralizerQuotientComponent L) ∧
    ∃ B : Subgroup G, BorelOverSylow L S B ∧ Yplus ≤ B)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics
