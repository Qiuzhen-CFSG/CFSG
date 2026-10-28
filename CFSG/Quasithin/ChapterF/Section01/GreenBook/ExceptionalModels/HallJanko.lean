module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Parity
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Seed
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Source markings for the Hall--Janko alternatives

For F.1.12(I)(10)--(11), the whole overlap is the source Borel
`N_L₁(S ∩ L₁) N_L₂(S ∩ L₂) S`. Normalization makes each full
parabolic a subgroup product, and gives normality of `Lᵢ` inside that
parabolic. The outer case need not have `S ≤ Lᵢ`.

These output contracts replace neither missing subgroup calculations nor
a recognition theorem. The predicates are tied to the exact ATLAS
permutation carrier and its full `MulAut`, and require only parabolic
equivalence. They assert no compatibility of arbitrary overlap maps.
The legacy arbitrary-carrier contracts remain available under their old
names, but are not used here. No theorem of the separate icosian model is
transported without a model equivalence.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, Hypothesis
F.1.1, Lemma F.1.3, and Proposition F.1.12(I)(10)--(11), printed pp.259--263.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.HallJanko
open Theory.GroupTheory
open Sporadic.LeechRelated.J2
open scoped Pointwise

/-- Marking data for the concrete exceptional models. `S` is Sylow, the
Borel is the source group `B₁B₂S`, and each local factor is normalized by it.
There is no requirement that the full `S` lie in either `Lᵢ`. -/
structure Marking (G : Type*) [Group G] where
  L : Fin 2 → Subgroup G
  S : Sylow 2 G
  borel_normalizes : ∀ i, Source.commonBorel L (S : Subgroup G) ≤
    Subgroup.normalizer (L i : Set G)
  overlap : (L 0 ⊔ Source.commonBorel L (S : Subgroup G)) ⊓
    (L 1 ⊔ Source.commonBorel L (S : Subgroup G)) = Source.commonBorel L (S : Subgroup G)
  generated : L 0 ⊔ L 1 ⊔ (S : Subgroup G) = ⊤

namespace Marking
variable {G : Type*} [Group G] (m : Marking G)

/-- The whole Borel, retaining both odd local Borel factors. -/
def B : Subgroup G := Source.commonBorel m.L (m.S : Subgroup G)
/-- The full parabolic `LᵢB`. -/
def P (i : Fin 2) : Subgroup G := m.L i ⊔ m.B
/-- The intermediate group `LᵢS`, distinct from `Lᵢ` in the outer case. -/
def LS (i : Fin 2) : Subgroup G := m.L i ⊔ (m.S : Subgroup G)

theorem S_le_B : (m.S : Subgroup G) ≤ m.B := le_sup_right

theorem L_le_P (i : Fin 2) : m.L i ≤ m.P i := le_sup_left

theorem B_le_P (i : Fin 2) : m.B ≤ m.P i := le_sup_right

/-- The stated parabolic is a subgroup product because the Borel normalizes `Lᵢ`. -/
theorem P_coe_eq_product (i : Fin 2) :
    (m.P i : Set G) = (m.L i : Set G) * (m.B : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ (m.borel_normalizes i)

/-- Normality is inside the full parabolic, rather than the ambient simple group. -/
theorem L_normal_in_P (i : Fin 2) : ((m.L i).subgroupOf (m.P i)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (m.L_le_P i)).mpr
    (sup_le (m.L i).le_normalizer (m.borel_normalizes i))

theorem P_generate : m.P 0 ⊔ m.P 1 = ⊤ := by
  apply top_unique
  rw [← m.generated]
  exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
    (m.S_le_B.trans (le_sup_right.trans le_sup_left))

/-- Inclusion of the entire common Borel gives the marked amalgam. -/
def amalgam : RankTwoAmalgam (m.P 0) m.B (m.P 1) :=
  RankTwoAmalgam.ofSubgroups _ _ _ (m.B_le_P 0) (m.B_le_P 1)

theorem left_injective : Function.Injective m.amalgam.left :=
  RankTwoAmalgam.ofSubgroups_left_injective _ _ _ (m.B_le_P 0) (m.B_le_P 1)

theorem right_injective : Function.Injective m.amalgam.right :=
  RankTwoAmalgam.ofSubgroups_right_injective _ _ _ (m.B_le_P 0) (m.B_le_P 1)

end Marking

/-- The four local calculations of F.1.12(I)(10), on the sourced degree-100 carrier.
This is an output contract; a witness still has to be constructed. -/
structure J2Model extends Marking Carrier where
  L₁_core : IsQuaternionDihedralCore (pCore 2 (L 0))
  L₁_quotient : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 4
  L₂_quotient : ClassicalGroup.IsPSL ((L 1) ⧸ pCore 2 (L 1)) 2 2
  L₂_core_card : Nat.card (pCore 2 (L 1)) = 64

/-- Output contract for the four local calculations of F.1.12(I)(11).
It can be checked in the permutation extension and transported to the full
automorphism group. Only the first quotient has numerator `L₁S`; the first
core remains intrinsic to `L₁`. -/
structure AutLocalModel (G : Type*) [Group G] extends Marking G where
  L₁S_quotient : Nonempty
    ((toMarking.LS 0 ⧸ pCore 2 (toMarking.LS 0)) ≃* Equiv.Perm (Fin 5))
  L₁_core : IsQuaternionDihedralCore (pCore 2 (L 0))
  L₂_quotient : Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* Equiv.Perm (Fin 3))
  L₂_core_card : Nat.card (pCore 2 (L 1)) = 64

/-- The full automorphism-group model used in the source alternative. -/
abbrev AutJ2Model := AutLocalModel (MulAut Carrier)

/-- The finite permutation extension on which the local calculations can
be made independently of its identification with the full automorphism group. -/
abbrev ExtensionModel := AutLocalModel ExceptionalParabolics.Extension

variable {L B R : Type*} [Group L] [Group B] [Group R]

/-- Recognition means parabolic equivalence to a marked model on the fixed carrier. -/
def IsJ2ParabolicModel (α : RankTwoAmalgam L B R) : Prop :=
  ∃ m : J2Model, Nonempty (RankTwoAmalgam.ParabolicEquiv α m.toMarking.amalgam)

/-- The automorphism alternative is likewise parabolic-only and tied to the full `MulAut`. -/
def IsAutJ2ParabolicModel (α : RankTwoAmalgam L B R) : Prop :=
  ∃ m : AutJ2Model, Nonempty (RankTwoAmalgam.ParabolicEquiv α m.toMarking.amalgam)

end CFSG.Quasithin.ChapterF.GreenBook.HallJanko
