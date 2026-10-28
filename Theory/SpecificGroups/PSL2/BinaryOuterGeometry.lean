module

public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.OuterInvolutions
public import Theory.SpecificGroups.PSL2.OuterSolvable.BinaryCyclic
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Outer elementary actors on binary PSL₂

For an elementary abelian subgroup A outside a self-centralizing normal
copy L of PSL₂(2^r), choose an outer involution t in A. Its literal layer
centralizer is PSL₂(2^m), where r = 2*m. The kernel of the cyclic outer
projection embeds in this centralizer, so |A| is at most 2^(m+1).
If A meets L trivially, the same projection bounds |A| by two.

The fixed-group equivalence also proves that L ∩ C_G(t) has trivial
two-core, including m = 1. This is the group input to Guralnick--Malle,
Classification of 2F-modules II, Proposition 4.1(2)--(3), manuscript p.22.
The Sylow equivalence with the additive field retains the half-degree
bound needed for the outer branch.
-/

public section
open scoped MatrixGroups IsMulCommutative
open Subgroup Theory.PSL2
namespace Theory.PSL2.BinaryOuterGeometry

private theorem twoGroup_card_le {F D : Type*} [Field F] [Finite F] [CharP F 2]
    [_root_.Group D] [Finite D] (hD : IsPGroup 2 D)
    (f : D →* Group F) (hf : Function.Injective f) : Nat.card D ≤ Nat.card F := by
  let j := (sl2QuotientEquiv F).symm.toMonoidHom.comp f
  have hj : Function.Injective j := (sl2QuotientEquiv F).symm.injective.comp hf
  have hp : IsPGroup 2 j.range := hD.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  calc
    Nat.card D = Nat.card j.range := Nat.card_congr (MonoidHom.ofInjective hj).toEquiv
    _ ≤ Nat.card P := Nat.card_le_card_of_injective
      (Subgroup.inclusion hP) (Subgroup.inclusion_injective hP)
    _ = Nat.card F :=
      (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P).toEquiv).symm

variable {G : Type*} [_root_.Group G] [Finite G]
  (L : Subgroup G) [L.Normal] {r : ℕ} (e : L ≃* BinaryGroup r)
  (hCL : centralizer (L : Set G) = ⊥)

private noncomputable def actor : G →* MulAut (BinaryGroup r) :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

omit [Finite G] in
include hCL in
private theorem actor_inner_iff (g : G) :
    actor L e g ∈ MulAut.innerSubgroup (BinaryGroup r) ↔ g ∈ L := by
  change MulAut.congr e (MulAut.conjNormal g) ∈ MulAut.innerSubgroup _ ↔ g ∈ L
  rw [← MulAut.map_innerSubgroup_congr e, Subgroup.mem_map_equiv]
  simp only [MulEquiv.symm_apply_apply]
  change g ∈ (MulAut.innerSubgroup L).comap MulAut.conjNormal ↔ g ∈ L
  rw [MulAut.conjNormal_comap_innerSubgroup, hCL, sup_bot_eq]

private def fixedEquiv (t : G) :
    ↥(L ⊓ centralizer {t}) ≃* (MulAut.conjNormal (H := L) t).fixedSubgroup where
  toFun x := ⟨⟨x, x.property.1⟩, by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    change t * (x : G) * t⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp x.property.2).symm⟩
  invFun x := ⟨x.val.val, x.val.property, by
    change (x.val : G) ∈ centralizer {t}
    rw [mem_centralizer_singleton_iff]
    have hx := (MulAut.mem_fixedSubgroup (MulAut.conjNormal (H := L) t) x.val).mp x.property
    have h := congrArg Subtype.val hx
    change t * (x.val : G) * t⁻¹ = x.val at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

include e hCL

omit [Finite G] in
/-- Descent of the actual layer centralizer of an outer involution. -/
theorem outer_fixed_model (hr : 2 ≤ r) (t : G) (ht : t ^ 2 = 1) (htL : t ∉ L) :
    ∃ m : ℕ, 0 < m ∧ r = 2 * m ∧
      Nonempty (↥(L ⊓ centralizer {t}) ≃* BinaryGroup m) := by
  let a := actor L e t
  have ha : a ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have hout : ¬ ∃ b : BinaryGroup r, a = MulAut.conj b := by
    rintro ⟨b, hb⟩
    apply htL
    exact (actor_inner_iff L e hCL t).mp ⟨b, hb.symm⟩
  obtain ⟨g, σ, heq⟩ := BenderSuzuki.ZD.Linear.semilinear_coverage a
  obtain ⟨m, hm, hrm, ⟨f⟩⟩ := outer_fixed_model_of_semilinear hr a ha g σ heq hout
  exact ⟨m, hm, hrm, ⟨(fixedEquiv L t).trans
    ((MulAut.fixedSubgroupCongr e (MulAut.conjNormal t)).trans f)⟩⟩

omit [Finite G] in
/-- The descended centralizer has trivial two-core even over GF(2). -/
theorem outer_fixed_twoCore_eq_bot (hr : 2 ≤ r) (t : G)
    (ht : t ^ 2 = 1) (htL : t ∉ L) : pCore 2 ↥(L ⊓ centralizer {t}) = ⊥ := by
  obtain ⟨m, hm, _, ⟨f⟩⟩ := outer_fixed_model L e hCL hr t ht htL
  have hz : pCore 2 (BinaryGroup m) = ⊥ := Atlas.RankOneFieldAutomorphisms.psl_twoCore_eq_bot
  have he := pCore_map_iso 2 f
  rw [hz] at he
  apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
  simpa only [Subgroup.map_bot] using he

/-- The cyclic outer image contributes at most one generator; the kernel
lies in the half-degree fixed group. -/
theorem outer_elementary_card_bound (hr : 2 ≤ r) (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hAL : ¬ A ≤ L) :
    ∃ m : ℕ, 0 < m ∧ r = 2 * m ∧ Nat.card A ≤ 2 ^ (m + 1) ∧
      (A ⊓ L = ⊥ → Nat.card A ≤ 2) := by
  obtain ⟨t, htA, htL⟩ := SetLike.not_le_iff_exists.mp hAL
  have ht : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t htA
  obtain ⟨m, hm, hrm, ⟨f⟩⟩ := outer_fixed_model L e hCL hr t ht htL
  let q := (QuotientGroup.mk' (MulAut.innerSubgroup (BinaryGroup r))).comp (actor L e)
  have hq (x : G) : q x = 1 ↔ x ∈ L :=
    (QuotientGroup.eq_one_iff _).trans (actor_inner_iff L e hCL x)
  let p := q.comp A.subtype
  let j : p.ker →* ↥(L ⊓ centralizer {t}) := {
    toFun x := ⟨x.val.val, (hq _).mp x.property, by
      change (x.val : G) ∈ centralizer {t}
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mul_comm x.val (⟨t, htA⟩ : A))⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(L ⊓ centralizer {t}) => (z : G)) he
  have hker : Nat.card p.ker ≤ 2 ^ m :=
    (twoGroup_card_le ((IsElementaryAbelian.isPGroup 2 A).to_subgroup p.ker)
      (f.toMonoidHom.comp j) (f.injective.comp hj)).trans_eq (GaloisField.card 2 m hm.ne')
  let : IsCyclic (MulAut.Outer (BinaryGroup r)) :=
    OuterSolvable.outer_isCyclic_of_field_coverage BenderSuzuki.ZD.Linear.semilinear_coverage
  have hrange : Nat.card p.range ≤ 2 := by
    apply Nat.le_of_dvd (by decide)
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    obtain ⟨b, hb⟩ := x.property
    apply Subtype.ext
    change (x : MulAut.Outer (BinaryGroup r)) ^ 2 = 1
    rw [← hb, ← map_pow]
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) b, map_one]
  have hcard : Nat.card A = Nat.card p.ker * Nat.card p.range := by
    rw [← Subgroup.index_ker, p.ker.card_mul_index]
  refine ⟨m, hm, hrm, ?_, ?_⟩
  · calc
      Nat.card A = Nat.card p.ker * Nat.card p.range := hcard
      _ ≤ 2 ^ m * 2 := Nat.mul_le_mul hker hrange
      _ = 2 ^ (m + 1) := (pow_succ 2 m).symm
  · intro hinter
    have hzero : p.ker = ⊥ := by
      apply p.ker.eq_bot_iff_forall.mpr
      intro x hx
      have hxL := (hq x).mp hx
      have hi : (x : G) ∈ A ⊓ L := ⟨x.property, hxL⟩
      rw [hinter, mem_bot] at hi
      exact Subtype.ext hi
    rw [hcard, hzero, Subgroup.card_bot, one_mul]
    exact hrange

end Theory.PSL2.BinaryOuterGeometry
