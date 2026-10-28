module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.DeletedPointIrreducible
public import Theory.GroupTheory.CComponent.SolvableSupplement
public import Theory.GroupTheory.CComponent.RadicalFree
public import Theory.GroupTheory.Commutator.PerfectQuotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The C-component of a marked deleted-point centralizer

The A₅ action on the translation sixteen-group is irreducible and nontrivial.
Its commutators therefore generate that entire kernel. Since the A₅ quotient
is perfect, the point block is perfect too. The C-component correspondence
through the abelian kernel then makes it a C-component of itself. Normality
in a supplied overgroup transports this conclusion through the actual inclusion.

Source: Aschbacher--Smith, 14.3.20, printed pp.997--998; Definition A.3.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace BinaryPermutation.SixNaturalSplit
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem pointBlock_isPerfect
    (K A : Subgroup G) [IsElementaryAbelian 2 A] (hcard : Nat.card A = 16)
    (f : K ≃* Model) (hA : (A.subgroupOf K).map f.toMonoidHom = translations)
    (hAK : A ≤ K) (d : normalizer (K : Set G))
    (hd : MulAut.congr f (K.normalizerMonoidHom d) = pointAutomorphism)
    (hAB : A ≤ K ⊓ centralizer ({(d : G)} : Set G)) :
    Group.IsPerfect (K ⊓ centralizer ({(d : G)} : Set G) : Subgroup G) := by
  let B := K ⊓ centralizer ({(d : G)} : Set G)
  obtain ⟨hn, ⟨e⟩⟩ := pointBlockCentralizer_quotient K A f hA d hd
  let := hn
  have hBA : B ≤ normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hAB).mp hn
  have hcomm : ⁅A,B⁆ = A := by
    rcases pointBlock_invariant_factor K A ⁅A,B⁆ f hA hAK d hd
      (le_normalizer_iff_commutator_le_left.mp hBA)
      (normalizer_commutator_ge_right A B) with hb | he
    · have hAC : A ≤ centralizer (B : Set G) :=
        commutator_eq_bot_iff_le_centralizer.mp hb
      have he := pointBlock_factor_centralizer K A hcard f hA hAK d hd
      change A ⊓ centralizer (B : Set G) = ⊥ at he
      rw [inf_of_le_left hAC] at he
      have hc1 : Nat.card A = 1 := Subgroup.card_eq_one.mpr he
      omega
    · exact he
  let q : B →* alternatingGroup (Fin 5) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (A.subgroupOf B))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = A.subgroupOf B := by
    ext x
    change e (QuotientGroup.mk' (A.subgroupOf B) x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hker : q.ker ≤ _root_.commutator B := by
    rw [hk]
    apply (map_le_map_iff_of_injective B.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hAB, map_commutator_eq, range_subtype]
    rw [← hcomm]
    exact commutator_mono hAB le_rfl
  exact ⟨(sup_of_le_right hker).symm.trans
    (CentralExtension.ker_sup_commutator_eq_top_of_surjective q hq)⟩

theorem pointBlock_isCComponent_top
    (K A : Subgroup G) [IsElementaryAbelian 2 A] (hcard : Nat.card A = 16)
    (f : K ≃* Model) (hA : (A.subgroupOf K).map f.toMonoidHom = translations)
    (hAK : A ≤ K) (d : normalizer (K : Set G))
    (hd : MulAut.congr f (K.normalizerMonoidHom d) = pointAutomorphism)
    (hAB : A ≤ K ⊓ centralizer ({(d : G)} : Set G)) :
    (⊤ : Subgroup (K ⊓ centralizer ({(d : G)} : Set G) : Subgroup G)).IsCComponent := by
  let B := K ⊓ centralizer ({(d : G)} : Set G)
  let := pointBlock_isPerfect K A hcard f hA hAK d hd hAB
  obtain ⟨hn, ⟨e⟩⟩ := pointBlockCentralizer_quotient K A f hA d hd
  let := hn
  let q : B →* alternatingGroup (Fin 5) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (A.subgroupOf B))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = A.subgroupOf B := by
    ext x
    change e (QuotientGroup.mk' (A.subgroupOf B) x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  let : Group.IsSolvable q.ker := by
    rw [hk]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hAB).toMonoidHom) (subgroupOfEquivOfLe hAB).injective
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup (⊤ : Subgroup (alternatingGroup (Fin 5))) :=
    topEquiv.isSimpleGroup
  have ha : (⊤ : Subgroup (alternatingGroup (Fin 5))).IsCComponent :=
    isCComponent_of_isSimpleGroup_of_isPerfect IsSubnormal.top
  have hh := residual_isCComponent_of_surjective q hq (by
    rwa [solvableResidual_eq_top])
  rwa [solvableResidual_eq_top] at hh

end BinaryPermutation.SixNaturalSplit
