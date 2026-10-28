module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.NormalizerAction.WreathModel

/-!
# The central involution and the nonsingular fixed plane

For the literal orthogonal wreath action, the central involution in the
standard dihedral Sylow actor has displacement image containing the vectors
fixed by its base subgroup. Every nontrivial normal subgroup of that Sylow
actor contains this involution. Sylow conjugacy transports both facts together.

The six vectors supported in one definite plane and the nine supported in
both planes are the two nonzero orbits. The quadratic identity shows that an
invariant quadratic function vanishing on the first orbit vanishes everywhere.
Thus every nonzero invariant quadratic function has a nonsingular vector in
the base fixed plane. All finite calculations are checked by kernel reduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the orthogonal
setup on printed pp.1121–1122 and the calculation in 15.3.49(m), p.1144.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.NormalizerAction.WreathModel
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.FixedPlane.Model

attribute [local instance] orthogonalAction
private instance : SMul OrthogonalActor OrthogonalVector := orthogonalAction.toMulAction.toSMul
private instance : MulAction OrthogonalActor OrthogonalVector := orthogonalAction.toMulAction

private instance : DecidableEq OrthogonalActor :=
  fun a b => decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    RegularWreathProduct.ext_iff.symm
private instance : Fintype OrthogonalActor :=
  Fintype.ofEquiv ((OrthogonalPlaneIndex → OrthogonalPlaneActor) × OrthogonalPlaneIndex)
    (RegularWreathProduct.equivProd _ _).symm


set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
private theorem dihedral_generate : ∀ x : DihedralGroup 4, x ≠ 1 →
    DihedralGroup.r 2 = x ∨ DihedralGroup.r 2 = x*x ∨
      ∃ g : DihedralGroup 4, DihedralGroup.r 2 = g*x*g⁻¹*x := by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
private theorem standard_image : ∀ v : OrthogonalVector,
    (∀ h : DihedralGroup 4, (wreathTwoDihedralHom h).right = 1 →
        wreathTwoDihedralHom h • v = v) →
    ∃ u : OrthogonalVector, v =
      (wreathTwoDihedralHom (DihedralGroup.r 2) • u) * u⁻¹ := by decide +kernel

private def e : OrthogonalVector := fun i =>
  if i = 1 then Multiplicative.ofAdd ![1,0] else 1
private def f : OrthogonalVector := fun i =>
  if i = 1 then Multiplicative.ofAdd ![0,1] else 1
private def g : OrthogonalVector := fun i =>
  if i = 1 then 1 else Multiplicative.ofAdd ![1,0]

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
private theorem standard_e :
    ∀ h : DihedralGroup 4, (wreathTwoDihedralHom h).right = 1 →
      wreathTwoDihedralHom h • e = e := by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
private theorem vector_orbits : ∀ v : OrthogonalVector,
    v = 1 ∨ (∃ a : OrthogonalActor, a • e = v) ∨
      (∃ a : OrthogonalActor, a • (e*g) = v) := by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
private theorem triple_orbits :
    (∃ a : OrthogonalActor, a • e = f) ∧
    (∃ a : OrthogonalActor, a • e = g) ∧
    (∃ a : OrthogonalActor, a • e = e*f) ∧
    (∃ a : OrthogonalActor, a • (e*g) = f*g) ∧
    (∃ a : OrthogonalActor, a • (e*g) = e*f*g) := by decide +kernel

private theorem invariant_zero_of_e_zero (q : OrthogonalVector → ZMod 2)
    (h1 : q 1 = 0) (hinv : ∀ a : OrthogonalActor, ∀ v, q (a • v) = q v)
    (hquad : ∀ x y z, q (x*y*z) + (q x + q y + q z) =
      q (x*y) + q (y*z) + q (z*x))
    (he : q e = 0) : ∀ v, q v = 0 := by
  have horbit {x y : OrthogonalVector} (h : ∃ a : OrthogonalActor, a • x = y) :
      q y = q x := by obtain ⟨a, rfl⟩ := h; exact hinv a x
  obtain ⟨hf, hg, hef, hfg, hefg⟩ := triple_orbits
  have ht := hquad e f g
  rw [horbit hf, horbit hg, horbit hef, horbit hfg, horbit hefg, mul_comm g e, he] at ht
  simp only [add_zero, zero_add] at ht
  have hzero : q (e*g) = 0 := by
    have hc := add_left_cancel (show q (e*g) + 0 = q (e*g) + q (e*g) by simpa using ht)
    exact hc.symm
  intro v
  rcases vector_orbits v with rfl | h | h
  · exact h1
  · exact (horbit h).trans he
  · exact (horbit h).trans hzero

private theorem fixed_conj (P : Subgroup OrthogonalActor)
    (a : OrthogonalActor) (v : OrthogonalVector) :
    baseFixed (MulAut.conj a • P) (a • v) ↔ baseFixed P v := by
  constructor
  · intro hv h hh hr
    have hh' : a * h * a⁻¹ ∈ MulAut.conj a • P :=
      Subgroup.smul_mem_pointwise_smul h (MulAut.conj a) P hh
    have he := hv _ hh' (by simpa [mul_assoc] using hr)
    apply MulAction.injective a
    simpa only [mul_smul, inv_smul_smul] using he
  · intro hv h hh hr
    have hh' : a⁻¹ * h * a ∈ P :=
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hh
    have he := hv _ hh' (by simpa [mul_assoc] using hr)
    have he' := congrArg (fun w : OrthogonalVector => a • w) he
    simpa only [mul_smul, smul_inv_smul] using he'

private theorem dihedral_center_mem {D : Type*} [Group D]
    (f : DihedralGroup 4 →* D) (Q : Subgroup D)
    (hle : Q ≤ f.range) (hne : Q ≠ ⊥)
    (hn : f.range ≤ normalizer (Q : Set D)) : f (DihedralGroup.r 2) ∈ Q := by
  obtain ⟨x, hx, hx1⟩ := Q.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨h, rfl⟩ := hle hx
  have hh : h ≠ 1 := by intro he; exact hx1 (by rw [he, map_one])
  rcases dihedral_generate h hh with he | he | ⟨g, he⟩
  · rwa [he]
  · rw [he, map_mul]; exact Q.mul_mem hx hx
  · rw [he, map_mul, map_mul, map_mul, map_inv]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hn ⟨g, rfl⟩) _).mp hx) hx

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
private theorem standard_center :
    wreathTwoDihedralHom (DihedralGroup.r 2) ≠ 1 ∧
    wreathTwoDihedralHom (DihedralGroup.r 2) ^ 2 = 1 ∧
    ∀ h : DihedralGroup 4,
      wreathTwoDihedralHom h * wreathTwoDihedralHom (DihedralGroup.r 2) =
      wreathTwoDihedralHom (DihedralGroup.r 2) * wreathTwoDihedralHom h := by decide +kernel

/-- The central involution of the actual Sylow actor lies in every nontrivial
normal subgroup and its displacement image contains the base fixed space. -/
theorem sylow_fixed_commutator (P : Sylow 2 OrthogonalActor)
    (Q : Subgroup OrthogonalActor) (hQP : Q ≤ P) (hQ : Q ≠ ⊥)
    (hn : (P : Subgroup OrthogonalActor) ≤ normalizer (Q : Set OrthogonalActor)) :
    ∃ z ∈ Q, z ≠ 1 ∧ z ^ 2 = 1 ∧
      (∀ p ∈ (P : Subgroup OrthogonalActor), p*z = z*p) ∧
      ∀ v, baseFixed (P : Subgroup OrthogonalActor) v →
        ∃ u : OrthogonalVector, v = (z • u)*u⁻¹ := by
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq OrthogonalActor wreathTwoSylow P
  rw [Sylow.coe_subgroup_smul] at hQP hn ⊢
  let f := (MulAut.conj a).toMonoidHom.comp wreathTwoDihedralHom
  have hr : f.range = MulAut.conj a • (wreathTwoSylow : Subgroup OrthogonalActor) := by
    rw [wreathTwoSylow_coe]
    exact MonoidHom.range_comp _ _
  have hz : f (DihedralGroup.r 2) ∈ Q :=
    dihedral_center_mem f Q (hQP.trans hr.symm.le) hQ (hr.le.trans hn)
  refine ⟨f (DihedralGroup.r 2), hz, ?_, ?_, ?_, ?_⟩
  · exact fun he => standard_center.1 ((MulAut.conj a).injective (by simpa [f] using he))
  · change (MulAut.conj a (wreathTwoDihedralHom (DihedralGroup.r 2))) ^ 2 = 1
    rw [← map_pow, standard_center.2.1, map_one]
  · intro p hp
    obtain ⟨h, rfl⟩ := hr.symm ▸ hp
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul] using
      congrArg (MulAut.conj a) (standard_center.2.2 h)
  · intro v hv
    have hv' : baseFixed (wreathTwoSylow : Subgroup OrthogonalActor) (a⁻¹ • v) :=
      (fixed_conj _ a (a⁻¹ • v)).mp (by simpa only [smul_inv_smul] using hv)
    have hstd : ∀ h : DihedralGroup 4, (wreathTwoDihedralHom h).right = 1 →
        wreathTwoDihedralHom h • (a⁻¹ • v) = a⁻¹ • v := by
      intro h hh
      exact hv' _ (wreathTwoSylow_coe.symm ▸ ⟨h, rfl⟩) hh
    obtain ⟨u, hu⟩ := standard_image _ hstd
    refine ⟨a • u, ?_⟩
    have hh := congrArg (fun w : OrthogonalVector => a • w) hu
    simpa only [smul_inv_smul, smul_mul', smul_inv', f, MonoidHom.comp_apply,
      MulAut.conj_apply, MulEquiv.coe_toMonoidHom, mul_smul, inv_smul_smul] using hh

/-- Every nonzero invariant quadratic function has a nonsingular vector in
the fixed plane. The quadratic identity rules out the spurious orbit labelling. -/
theorem sylow_fixed_nonsingular (P : Sylow 2 OrthogonalActor)
    (q : OrthogonalVector → ZMod 2) (h1 : q 1 = 0)
    (hinv : ∀ a : OrthogonalActor, ∀ v, q (a • v) = q v)
    (hquad : ∀ x y z, q (x*y*z) + (q x + q y + q z) =
      q (x*y) + q (y*z) + q (z*x))
    (hne : ¬ ∀ v, q v = 0) :
    ∃ v, baseFixed (P : Subgroup OrthogonalActor) v ∧ q v ≠ 0 := by
  have he : q e ≠ 0 := fun he => hne (invariant_zero_of_e_zero q h1 hinv hquad he)
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq OrthogonalActor wreathTwoSylow P
  refine ⟨a • e, ?_, by rwa [hinv]⟩
  rw [Sylow.coe_subgroup_smul]
  apply (fixed_conj _ a e).mpr
  intro h hh hr
  rw [wreathTwoSylow_coe] at hh
  obtain ⟨h, rfl⟩ := hh
  exact standard_e h hr

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.FixedPlane.Model
