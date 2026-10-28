module
public import Theory.Representation.OrthogonalFourPlusMatrix.Commutant
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Theory.SpecificGroups.SL2.NaturalStabilizer
public import Theory.SpecificGroups.SL2.OddAbelianSubgroups

/-!
# Inner component automorphisms lifted on the determinant module

A field-linear intertwiner on two natural columns preserves the trace of
an SL₂ element: g + g⁻¹ is its trace times the identity. This avoids taking
the trace of the four-dimensional operator, which vanishes in characteristic
two. Actual inner-field automorphism coverage and companion matrices then
make the component automorphism inner. An odd abelian subgroup fixing a
nonzero matrix is faithful on its second factor and hence cyclic.

The central Hall tensor argument applies this to its original seed action.
Source: Aschbacher--Smith 9.2.5--6 and 10.2.3, printed pp.731,745.
-/

public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups
namespace ClassicalOrthogonal.FourPlusMatrix
variable {F : Type*} [Field F]

private theorem sl2_add_inverse (g : SL(2,F)) :
    g.val + g⁻¹.val = g.val.trace • (1 : Mat (F := F)) := by
  rw [SpecialLinearGroup.coe_inv,adjugate_fin_two,trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

/-- A field-linear lift on the two-column natural module makes the original
component automorphism inner. The trace is recovered from g + g⁻¹, so the
argument also applies in characteristic two with an even number of copies. -/
theorem linear_left_intertwiner_inner [Finite F] [CharP F 2]
    (a : MulAut SL(2,F)) (E : Mat (F := F) ≃ₗ[F] Mat (F := F))
    (he : ∀ g v, E (g.val * v) = (a g).val * E v) :
    ∃ g, a = MulAut.conj g := by
  have htrace (g : SL(2,F)) : (a g).val.trace = g.val.trace := by
    have hh : E ((g.val + g⁻¹.val) * E.symm 1) =
        ((a g).val + (a g)⁻¹.val) * (1 : Mat (F := F)) := by
      rw [add_mul,E.map_add,he,he,map_inv,E.apply_symm_apply,add_mul]
    rw [sl2_add_inverse,sl2_add_inverse,smul_mul_assoc,one_mul,
      E.map_smul,E.apply_symm_apply,mul_one] at hh
    have h0 := congrArg (fun M : Mat (F := F) => M 0 0) hh
    simpa using h0.symm
  obtain ⟨g,δ,ha⟩ := Theory.PSL2.sl2_semilinear_coverage a
  have hδ : δ = RingEquiv.refl F := by
    ext t
    let k : SL(2,F) := ⟨!![0,-1;1,t],by simp [Matrix.det_fin_two]⟩
    have ht := htrace k
    have hconj : (g * Theory.PSL2.sl2FieldAut δ k * g⁻¹).val.trace =
        (Theory.PSL2.sl2FieldAut δ k).val.trace := by
      change Matrix.trace (g.val * (Theory.PSL2.sl2FieldAut δ k).val * (g⁻¹).val) = _
      rw [Matrix.trace_mul_cycle]
      change Matrix.trace ((g⁻¹ * g).val * (Theory.PSL2.sl2FieldAut δ k).val) = _
      simp
    rw [ha] at ht
    change (g * Theory.PSL2.sl2FieldAut δ k * g⁻¹).val.trace = k.val.trace at ht
    rw [hconj] at ht
    simp only [Matrix.trace_fin_two] at ht
    change δ 0 + δ t = 0 + t at ht
    simpa using ht
  refine ⟨g,?_⟩
  rw [ha,hδ]
  ext k i j
  change (g * Theory.PSL2.sl2FieldAut (RingEquiv.refl F) k * g⁻¹).val i j = (g*k*g⁻¹).val i j
  rfl

variable [CharP F 2]

/-- An odd subgroup fixing a nonzero determinant-module vector is faithful
on either factor. Here the second projection is the specified embedding. -/
theorem snd_injective_of_odd_fixed
    {A : Type*} [Group A] [Finite A]
    (r : A →* PairSL (F := F)) (hr : Function.Injective r)
    (ho : Odd (Nat.card A)) (v : Mat (F := F)) (hv : v ≠ 0)
    (hfix : ∀ a, matrixAction (r a) v = v) :
    Function.Injective ((MonoidHom.snd _ _).comp r) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  have har : (r a).2 = 1 := ha
  have hleft : (r a).1.val * v = v := by
    have hh := hfix a
    change (r a).1.val * v * (r a).2⁻¹.val = v at hh
    simpa only [har,inv_one,SpecialLinearGroup.coe_one,mul_one] using hh
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  obtain ⟨j,hij⟩ := Function.ne_iff.mp hi
  have hcol : (fun k => v k j) ≠ 0 := fun he => hij (congrFun he i)
  have h2 := Matrix.SL2.pow_two_eq_one_of_nonzero_fixed (r a).1 (fun k => v k j) hcol (by
    funext k
    exact congrArg (fun M : Mat (F := F) => M k j) hleft)
  have ho' : Odd (orderOf (r a).1) := ho.of_dvd_nat
    ((orderOf_map_dvd ((MonoidHom.fst _ _).comp r) a).trans (orderOf_dvd_natCard a))
  have h1 : (r a).1 = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ho'.coprime_two_right dvd_rfl
      (orderOf_dvd_of_pow_eq_one h2))
  apply mem_bot.mpr
  apply hr
  rw [map_one]
  exact Prod.ext h1 har

/-- The same faithful projection makes an odd abelian vector stabilizer cyclic. -/
theorem odd_abelian_fixed_isCyclic
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (r : A →* PairSL (F := F)) (hr : Function.Injective r)
    (ho : Odd (Nat.card A)) (v : Mat (F := F)) (hv : v ≠ 0)
    (hfix : ∀ a, matrixAction (r a) v = v) : IsCyclic A :=
  Matrix.SL2.odd_abelian_isCyclic_of_injective ho ((MonoidHom.snd _ _).comp r)
    (snd_injective_of_odd_fixed r hr ho v hv hfix)

end ClassicalOrthogonal.FourPlusMatrix
