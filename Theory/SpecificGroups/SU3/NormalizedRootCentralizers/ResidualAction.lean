module

public import Theory.SpecificGroups.SU3.CyclicNormalOuter
public import Theory.SpecificGroups.SU3.EvenSemilinear
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# The unitary residual has no field part

The quotient of Aut(PSU₃) by the actual inner-diagonal image is cyclic.
Thus D = [D,T] maps trivially to that quotient under every action. The
semilinear coverage theorem is proved for the binary model, using the
simplicity inherited from a component. No split extension is introduced.

Source: Aschbacher–Smith, A.3.16–18 and the identity Lᵥ = [Lᵥ,Tᵥ]
in the proof of 13.6.6, printed p.927; GLS3, Theorem 2.5.12.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace BenderSuzuki.MatrixGroups.HermitianForm.NormalizedRootCentralizers
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

omit [Finite E] in
/-- The genuine inner-diagonal subgroup contains the inner action. -/
theorem inner_le_unitary : MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) ≤
    J.unitaryConjHom.range := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨u, rfl⟩ := J.specialToProjective_surjective x
  exact ⟨⟨u.val, u.property.1⟩, by
    rw [J.unitaryConjHom_apply, J.unitaryConj_special_is_inner]⟩

/-- Commutator generation kills the actual quotient by inner-diagonal actors. -/
theorem commutator_generated_unitary
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n)^2)
    (hconj : ∀ x : E, J.conj x = x ^ (2^n))
    {H : Type*} [Group H] (f : H →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (D T : Subgroup H) (hD : ⁅D,T⁆ = D) : D.map f ≤ J.unitaryConjHom.range := by
  have hcover := EvenSemilinear.semilinear_coverage J hJ (by omega : 2 ≤ n) hcard hconj
  let N := J.unitaryOuterHom.range
  let : N.Normal := J.unitaryOuterHom_range_normal_of_semilinear_coverage hJ hcover
  let : IsCyclic (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J) ⧸ N) :=
    J.outer_mod_unitary_isCyclic_of_semilinear_coverage hJ hcover
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
  let g := (QuotientGroup.mk' N).comp (q.comp f)
  have hg : D.map g = ⊥ := by
    rw [← hD, map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr fun _ _ =>
      mem_centralizer_iff.mpr fun _ _ => mul_comm _ _
  rintro _ ⟨d, hd, rfl⟩
  have hdg : g d = 1 := by
    have hh := mem_map_of_mem g hd
    rwa [hg, mem_bot] at hh
  have hdq : q (f d) ∈ N := (QuotientGroup.eq_one_iff _).mp hdg
  have he : N.comap q = J.unitaryConjHom.range := by
    change J.unitaryOuterHom.range.comap q = _
    rw [unitaryOuterHom, MonoidHom.range_comp, comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr (inner_le_unitary J)
  exact he ▸ hdq
end BenderSuzuki.MatrixGroups.HermitianForm.NormalizedRootCentralizers
