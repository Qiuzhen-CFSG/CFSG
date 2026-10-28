module

public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.FieldDegree
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.GroupTheory.IsPerfect

/-!
# Centralizer generation for binary PSL₂ field involutions

The parameter-one upper and lower transvections are fixed by every field
automorphism. Their centralizers contain the respective root groups, and
transvection generation gives the whole projective group. Over a fixed field
with at least four elements, perfectness makes the fixed subgroup equal to
its two-residual. Thus the involutions used really belong to O²(C_L(r)).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the field
involution branch of Lemma 16.4.8, printed p.1188. All actions here are entrywise
field actions on the actual quotient SL₂/Z(SL₂); no model certificate is used.
-/

public section
open Subgroup Matrix

namespace Theory.PSL2
variable {K : Type*} [Field K] [CharP K 2]

private theorem transvection_one_order {i j : Fin 2} (hij : i ≠ j) :
    orderOf (quotientMap K (SpecialLinearGroup.transvection hij (1 : K))) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, pow_two, ← SpecialLinearGroup.transvection_add,
      CharTwo.add_self_eq_zero, SpecialLinearGroup.transvection_coeff_zero, map_one]
  · intro he
    have hc : SpecialLinearGroup.transvection hij (1 : K) ∈
        center (SpecialLinearGroup (Fin 2) K) := (QuotientGroup.eq_one_iff _).mp he
    exact one_ne_zero ((SpecialLinearGroup.transvection_mem_center_iff hij 1).mp hc)

/-- Fixed transvections supply both root groups. This also holds over GF(2). -/
theorem field_fixed_centralizers_generate (σ : K ≃+* K) :
    (⨆ (j : Group K) (_ : j ∈ (fieldAut σ).fixedSubgroup) (_ : orderOf j = 2),
      centralizer ({j} : Set (Group K))) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨A, rfl⟩ := quotientMap_surjective K x
  apply Matrix.SL2.transvection_induction
    (fun A => quotientMap K A ∈
      ⨆ (j : Group K) (_ : j ∈ (fieldAut σ).fixedSubgroup) (_ : orderOf j = 2),
        centralizer ({j} : Set (Group K))) ?_ ?_ A
  · intro i j hij c
    let u := quotientMap K (SpecialLinearGroup.transvection hij (1 : K))
    have hu : u ∈ (fieldAut σ).fixedSubgroup := by
      rw [MulAut.mem_fixedSubgroup]
      dsimp only [u]
      rw [fieldAut_apply_quotientMap]
      congr 1
      ext a b
      simp [SpecialLinearGroup.transvection_coe, Matrix.single, Matrix.one_apply]
    refine mem_iSup_of_mem u (mem_iSup_of_mem hu
      (mem_iSup_of_mem (transvection_one_order hij) ?_))
    rw [mem_centralizer_singleton_iff]
    change quotientMap K _ * quotientMap K _ = quotientMap K _ * quotientMap K _
    rw [← map_mul, ← map_mul, ← SpecialLinearGroup.transvection_add,
      ← SpecialLinearGroup.transvection_add, add_comm c 1]
  · intro A B hA hB
    rw [map_mul]
    exact mul_mem hA hB

/-- Perfectness over the actual fixed field eliminates every two-group quotient. -/
theorem fixed_twoResidual_eq_top [Finite K] (σ : K ≃+* K)
    (ha : ∃ a : FixedBy.subfield K σ, a ≠ 0 ∧ a ≠ 1) :
    pResidual 2 (fieldAut σ).fixedSubgroup = ⊤ := by
  obtain ⟨a, ha, ha1⟩ := ha
  have hc : commutator (Group (FixedBy.subfield K σ)) = ⊤ :=
    SL2Simple.PSL_commutator_eq_top ⟨a, ha, fun hs =>
      ha1 (CharTwo.sq_injective (by simpa using hs))⟩
  let : _root_.Group.IsPerfect (Group (FixedBy.subfield K σ)) := ⟨hc⟩
  let : _root_.Group.IsPerfect (fieldAut σ).fixedSubgroup :=
    _root_.Group.IsPerfect.ofSurjective (f := (fieldAutFixedEquiv σ).symm.toMonoidHom)
      (fieldAutFixedEquiv σ).symm.surjective
  apply (pResidual_eq_top_iff 2 _).mpr
  intro N hN hP
  let := hN
  have : Subsingleton ((fieldAut σ).fixedSubgroup ⧸ N) := by
    by_contra! hn
    exact _root_.Group.IsPerfect.not_isNilpotent _ hP.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The degree restriction excludes the nonperfect fixed group PSL₂(2). -/
theorem binary_fixed_twoResidual_eq_top {n : ℕ} (hn : 2 < n)
    (σ : BinaryField n ≃+* BinaryField n) (hs : Function.Involutive σ)
    (hne : σ ≠ RingEquiv.refl _) : pResidual 2 (fieldAut σ).fixedSubgroup = ⊤ := by
  apply fixed_twoResidual_eq_top
  have hc : 4 ≤ Nat.card (FixedBy.subfield (BinaryField n) σ) := by
    rw [binary_fixedField_card (by omega) σ hs hne]
    have hev := even_of_binary_field_involution (by omega) σ hs hne
    obtain ⟨m, hm⟩ := hev
    have hhalf : 2 ≤ n / 2 := by omega
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hhalf
  have hu : 1 < Nat.card (FixedBy.subfield (BinaryField n) σ)ˣ := by
    rw [Nat.card_units]
    omega
  let : Nontrivial (FixedBy.subfield (BinaryField n) σ)ˣ :=
    Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨u, hu⟩ := exists_ne (1 : (FixedBy.subfield (BinaryField n) σ)ˣ)
  exact ⟨u, u.ne_zero, fun he => hu (Units.val_eq_one.mp he)⟩

/-- The exact intrinsic generation equality used in source 16.4.8. -/
theorem binary_field_residual_centralizers_generate {n : ℕ} (hn : 2 < n)
    (σ : BinaryField n ≃+* BinaryField n) (hs : Function.Involutive σ)
    (hne : σ ≠ RingEquiv.refl _) :
    (⨆ (j : BinaryGroup n)
      (_ : j ∈ (pResidual 2 (fieldAut σ).fixedSubgroup).map
        (fieldAut σ).fixedSubgroup.subtype) (_ : orderOf j = 2),
      centralizer ({j} : Set (BinaryGroup n))) = ⊤ := by
  rw [binary_fixed_twoResidual_eq_top hn σ hs hne,
    ← MonoidHom.range_eq_map, range_subtype]
  exact field_fixed_centralizers_generate σ

end Theory.PSL2
