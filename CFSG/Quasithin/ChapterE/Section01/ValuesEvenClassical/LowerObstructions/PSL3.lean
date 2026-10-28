module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.Bounds
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSL3.Geometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSL3.CoreRank
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSL3.LargeIntersection
public import CFSG.Quasithin.ClassicalModels
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The PSL₃ lower obstruction in E.1.14(1)

The concrete two-plane family has weak closure equal to the matrix Sylow
subgroup and a proper normalizer. The literal quotient-rank bound for each
E-member forces its normal two-core to meet the actor plane in more than
2^f elements. The geometric normalizer dichotomy then puts the member in
the Sylow normalizer: its other alternative would make the actor plane a
normal two-subgroup, contradicting the active odd-prime or component clause.

All local premises are discharged below. The intrinsic centralizer and
two-core descriptions handle every ambient automorphism, including graph
and field automorphisms. In fact the lower obstruction holds for any normal
PSL₃(2^f) subgroup of a finite group, with f > 1. Applying it to F*(G)
proves the requested lower obstruction under the source SQTK, simplicity
and G = LT hypotheses without needing those additional restrictions.
The independent upper bound and the resulting equality n(G) = f are not
asserted here.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.1--6 and E.1.14(1), printed pp.209--211 and 214. The latter cites
Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.7.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.PSL3Obstruction
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- The actual two-plane family supplies the obstruction once its local
member calculation has been proved. No assumption about the outer action
is used to construct the family or its proper weak-closure normalizer. -/
theorem not_isEGenerated_of_plane_members_le (L : Subgroup G) [L.Normal]
    (e : L ≃* PSL(3,F)) {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2^f)
    (hmembers : ∀ T : Sylow 2 G, sylowImage L e ≤ (T : Subgroup G) →
      ∀ (b : Bool) (K : Subgroup G),
        IsEMemberAt (f - 1) (T : Subgroup G) (planeImage L e b) K →
        K ≤ normalizer (sylowImage L e : Set G)) :
    ¬ IsEGenerated (f - 1) G := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨T, hST⟩ := (sylowImage_isPGroup L e hF).exists_le_sylow
  apply not_isEGenerated_of_members_le T (planeFamily L f)
    (isElementaryFamily_planeFamily L f) (normalizer (sylowImage L e : Set G))
    (normalizer_sylowImage_ne_top L e)
  · rw [weakClosure_eq L e (by omega) hF T hST]
  · intro A hA hAT K hK
    obtain ⟨b, rfl⟩ := (family_le_sylow_iff L e (by omega) hF T hST A).mp ⟨hA, hAT⟩
    exact hmembers T hST b K hK

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.PSL3Obstruction

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical

open PSL3Obstruction
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The two-plane obstruction in every finite ambient extension of a normal
PSL₃(2^f) subgroup. The geometric and quotient-rank inputs are both proved. -/
theorem not_isEGenerated_of_normal_psl3 (L : Subgroup G) [L.Normal]
    {F : Type*} [Field F] [Finite F] {f : ℕ} (hf : 1 < f)
    (hcard : Nat.card F = 2 ^ f) (e : L ≃* PSL(3,F)) :
    ¬ IsEGenerated (f - 1) G :=
  not_isEGenerated_of_plane_members_le L e hf hcard
    (members_le_normalizer_sylowImage L e hf hcard
      (largeIntersectionNormalizer L e hf hcard))

/-- The PSL₃ lower obstruction in E.1.14(1), at the literal generalized
Fitting subgroup and with no additional local or outer-action premise. -/
theorem not_isEGenerated_of_psl3
    {F : Type*} [Field F] [Finite F] {f : ℕ} (hf : 1 < f)
    (hcard : Nat.card F = 2 ^ f) (e : generalizedFitting G ≃* PSL(3,F)) :
    ¬ IsEGenerated (f - 1) G :=
  not_isEGenerated_of_normal_psl3 (generalizedFitting G) hf hcard e

/-- Adapter for the concrete PSL₃ predicate consumed by the classical-value
assembly. Its field and multiplicative equivalence are used explicitly. -/
theorem not_isEGenerated_of_isPSL3 {f : ℕ} (hf : 1 < f)
    (hmodel : ClassicalGroup.IsPSL (generalizedFitting G) 3 (2 ^ f)) :
    ¬ IsEGenerated (f - 1) G := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hmodel
  exact not_isEGenerated_of_psl3 hf hcard e

end CFSG.Quasithin.ChapterE.ValuesEvenClassical
