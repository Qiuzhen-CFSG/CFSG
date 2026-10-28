module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.LowerObstruction.Family
public import Theory.GroupTheory.SolvableRadical.TwoClosedKernel
public import Theory.ElementaryAbelian.GeneratorRank
public import Mathlib.GroupTheory.Schreier

/-!
# The literal E₂ rank and its two-core kernel

The full ambient highest-root orbit consists of elementary groups of rank f.
For an E₂ member H the quotient image of A is nontrivial, in both the fixed
and permuted component alternatives. Two-closedness identifies its kernel
with A intersect O₂(H). If that kernel is trivial, the literal image in
H/O∞(H) has rank f. A rank deficit therefore gives a nontrivial, proper
intersection with O₂(H), not merely a small abstract group of rank f.

These are reductions for Aschbacher--Smith E.1.14(1), printed p.214,
citing Asc82a Lemma 4.7, using the definitions E.1.1--5 on pp.209--210.
The G₂ geometry excluding this proper kernel outside the short overgroup
is a separate remaining obligation. No quotient identification is assumed.
-/

public section

namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction.ComponentRank
open Subgroup Theory.GroupTheory Atlas.G2
open scoped IsMulCommutative
variable {G F : Type*} [Group G] [Finite G] [Field F] [CharP F 2]

/-- Rank of every member of the full ambient root orbit, including outer
conjugates. This statement concerns A before quotienting. -/
theorem rank_family_member (L : Subgroup G) (e : L ≃* Model F)
    {A : Subgroup G} (hA : A ∈ family L e) {f : ℕ}
    (hF : Nat.card F = 2 ^ f) : Group.rank A = f := by
  let _ := (family_elementary L e).1 A hA
  have hc : Nat.card A = 2 ^ f := (card_family_member L e hA).trans hF
  apply le_antisymm (IsElementaryAbelian.rank_le_of_card_le A hc.le)
  apply (Nat.pow_dvd_pow_iff_le_right Nat.one_lt_two).mp
  rw [← hc]
  exact card_dvd_exponent_pow_rank' A
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A))

omit [Field F] [CharP F 2] in
/-- The source two-closed radical clause identifies the two actual kernels. -/
theorem component_inf_radical_eq_core {T A H : Subgroup G}
    (hm : IsEMember T A H) (hc : ECaseComponent T A H) :
    A.subgroupOf H ⊓ solvableRadical H = A.subgroupOf H ⊓ pCore 2 H := by
  let _ := hm.1
  let _ := IsElementaryAbelian.subgroupOf (p := 2) hm.2.2.1
  exact inf_solvableRadical_eq_inf_pCore _
    (IsElementaryAbelian.isPGroup 2 (A.subgroupOf H)) hc.1

omit [Field F] [CharP F 2] in
/-- The E₂ image rank equals the image rank modulo the intrinsic two-core.
The equality is obtained from equal kernels, not an assumed quotient model. -/
theorem component_rank_eq_core {T A H : Subgroup G}
    (hm : IsEMember T A H) (hc : ECaseComponent T A H) :
    Group.rank ((A.subgroupOf H).map (QuotientGroup.mk' (solvableRadical H))) =
      Group.rank ((A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) :=
  rank_quotientImage_eq_of_inf_eq _ _ _ (component_inf_radical_eq_core hm hc)

omit [Field F] [CharP F 2] in
/-- Neither source component alternative permits the image of A to vanish. -/
theorem component_image_ne_bot {T A H : Subgroup G}
    (hc : ECaseComponent T A H) :
    (A.subgroupOf H).map (QuotientGroup.mk' (solvableRadical H)) ≠ ⊥ := by
  intro hz
  obtain ⟨_, _, _, D, hD, _, hd | hn⟩ := hc
  · rw [hz, commutator_bot_right] at hd
    have hs := hD.2.simple
    rw [hd] at hs
    let _ := hs
    exact not_nontrivial_iff_subsingleton.mpr
      (inferInstance : Subsingleton ((⊥ : Subgroup (H ⧸ solvableRadical H)) ⧸
        center (⊥ : Subgroup (H ⧸ solvableRadical H)))) hs.toNontrivial
  · exact hn.1 (hz ▸ bot_le)

omit [Field F] [CharP F 2] in
/-- In particular the E₂ actor is not contained in the intrinsic two-core. -/
theorem component_not_le_core {T A H : Subgroup G}
    (hm : IsEMember T A H) (hc : ECaseComponent T A H) :
    ¬ A.subgroupOf H ≤ pCore 2 H := by
  intro hle
  have hrad : A.subgroupOf H ≤ solvableRadical H := by
    have hi := component_inf_radical_eq_core hm hc
    rw [inf_eq_left.mpr hle] at hi
    exact inf_eq_left.mp hi
  apply component_image_ne_bot hc
  apply bot_unique
  rintro _ ⟨a, ha, rfl⟩
  exact (QuotientGroup.eq_one_iff _).mpr (hrad ha)

/-- With a trivial kernel the quotient image really is isomorphic to A,
so its generator rank is f. -/
theorem rank_radical_eq_of_inf_eq_bot (L : Subgroup G) (e : L ≃* Model F)
    {A H : Subgroup G} (hA : A ∈ family L e) (hAH : A ≤ H)
    {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hker : A.subgroupOf H ⊓ solvableRadical H = ⊥) :
    Group.rank ((A.subgroupOf H).map (QuotientGroup.mk' (solvableRadical H))) = f := by
  let B := A.subgroupOf H
  let q := QuotientGroup.mk' (solvableRadical H)
  have hinj : Function.Injective (q.subgroupMap B) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    have hxq : q x.val = 1 := congrArg Subtype.val (show q.subgroupMap B x = 1 from hx)
    have hxR := (QuotientGroup.eq_one_iff x.val).mp hxq
    exact (show x.val ∈ (⊥ : Subgroup H) from hker ▸ ⟨x.property, hxR⟩)
  let eqv := MulEquiv.ofBijective (q.subgroupMap B)
    ⟨hinj, q.subgroupMap_surjective B⟩
  exact (Group.rank_congr eqv).symm.trans
    ((Group.rank_congr (subgroupOfEquivOfLe hAH)).trans (rank_family_member L e hA hF))

/-- A rank deficit in the literal radical quotient produces a nonzero
proper two-core kernel. This is the exact input needed by the local geometry. -/
theorem proper_core_kernel_of_rank_lt (L : Subgroup G) (e : L ≃* Model F)
    {T A H : Subgroup G} (hA : A ∈ family L e)
    (hm : IsEMember T A H) (hc : ECaseComponent T A H)
    {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hr : Group.rank ((A.subgroupOf H).map
      (QuotientGroup.mk' (solvableRadical H))) < f) :
    A.subgroupOf H ⊓ pCore 2 H ≠ ⊥ ∧ ¬ A.subgroupOf H ≤ pCore 2 H := by
  refine ⟨?_, component_not_le_core hm hc⟩
  intro hz
  have he := rank_radical_eq_of_inf_eq_bot L e hA hm.2.2.1 hF
    ((component_inf_radical_eq_core hm hc).trans hz)
  omega

end CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction.ComponentRank
