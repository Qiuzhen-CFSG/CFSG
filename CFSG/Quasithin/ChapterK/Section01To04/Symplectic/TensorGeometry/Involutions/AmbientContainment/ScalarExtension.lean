module
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Descent
public import Theory.Representation.SchurDisplacement

/-!
# Schur linearity of displacement fixers and scalar extension

An ambient element fixing a nonzero component displacement commutes with the
actual Schur field. Conjugating a component endomorphism and subtracting the
original gives an intertwiner killing a nonzero displaced vector; irreducibility
forces that difference to vanish. The resulting Schur-linear operator extends
through the published tensor identification and preserves the literal
conjugation and displacement identities.

Source: Aschbacher–Smith, K.3.4.2, printed p.457 (PDF p.468).
-/

public section
set_option linter.unusedSimpArgs false
open Representation Representation.BinaryOffender
open scoped TensorProduct
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.AmbientContainment
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]

private def conjugateEnd (g : G)
    (f : IntertwiningMap (ρ.comp L.subtype) (ρ.comp L.subtype)) :
    IntertwiningMap (ρ.comp L.subtype) (ρ.comp L.subtype) where
  toLinearMap := ρ g * f.toLinearMap * ρ g⁻¹
  isIntertwining' x := by
    let x' : L := ⟨g⁻¹ * x * g, by
      simpa using (inferInstance : L.Normal).conj_mem x.val x.property g⁻¹⟩
    ext v
    change ρ g (f (ρ g⁻¹ (ρ x v))) = ρ x (ρ g (f (ρ g⁻¹ v)))
    have hmove : ρ g⁻¹ (ρ x v) = ρ (x' : G) (ρ g⁻¹ v) := by
      simp only [x', map_mul, Module.End.mul_apply]
      simp
    rw [hmove]
    change ρ g (f ((ρ.comp L.subtype) x' (ρ g⁻¹ v))) = _
    rw [f.isIntertwining]
    change ρ g (ρ (x' : G) (f (ρ g⁻¹ v))) = _
    simp only [x', map_mul, Module.End.mul_apply]
    simp

variable [IsIrreducible (ρ.comp L.subtype)]

/-- Fixing a nonzero component displacement forces linearity over its actual Schur field. -/
theorem displacement_fixer_isSchurLinear (hf : Function.Injective ρ)
    (j : G) (hjL : j ∈ L) (hj : j ≠ 1) (g : G)
    (hfix : ∀ v, ρ g (displacement ρ j v) = displacement ρ j v) :
    Representation.IsSchurLinear ρ L g := by
  have hex : ∃ v, displacement ρ j v ≠ 0 := by
    by_contra! hh
    apply hj
    apply hf
    ext v
    simpa only [displacement, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero, map_one, Module.End.one_apply] using hh v
  obtain ⟨v, hv⟩ := hex
  intro f
  let w := displacement ρ j v
  have hw : ρ g w = w := hfix v
  have hiw : ρ g⁻¹ w = w := by
    have he := congrArg (ρ g⁻¹) hw
    simpa using he.symm
  have hfw : f w = displacement ρ j (f v) := by
    change f (ρ j v - v) = ρ j (f v) - f v
    rw [map_sub]
    have he := congrArg (fun A : Module.End (ZMod 2) V => A v)
      (f.isIntertwining' (⟨j, hjL⟩ : L))
    exact congrArg (· - f v) he
  have hz : (conjugateEnd ρ L g f - f) w = 0 := by
    change ρ g (f (ρ g⁻¹ w)) - f w = 0
    rw [hiw, hfw, hfix, sub_self]
  have he : conjugateEnd ρ L g f = f := by
    rcases IsIrreducible.injective_or_eq_zero (conjugateEnd ρ L g f - f) with hi | he
    · exact False.elim (hv (hi (hz.trans (map_zero _).symm)))
    · exact sub_eq_zero.mp he
  have hh := congrArg (fun f : IntertwiningMap (ρ.comp L.subtype) (ρ.comp L.subtype) =>
    f.toLinearMap * ρ g) he
  change ρ g * f.toLinearMap = f.toLinearMap * ρ g
  simpa only [conjugateEnd, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] using hh

end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.AmbientContainment

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.AmbientContainment
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {G V F : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  [IsIrreducible (ρ.comp L.subtype)] [Field F]
  [Algebra (SchurField (ρ.comp L.subtype)) F]

/-- The original actor, linear over the actual component endomorphism field. -/
noncomputable def schurActor (g : G) (hg : Representation.IsSchurLinear ρ L g) :
    (Representation.asModule (ρ.comp L.subtype)) ≃ₗ[SchurField (ρ.comp L.subtype)]
      (Representation.asModule (ρ.comp L.subtype)) :=
  LinearEquiv.ofBijective
    { toFun := fun v => (Representation.asModuleEquiv (ρ.comp L.subtype)).symm
        (ρ g ((Representation.asModuleEquiv (ρ.comp L.subtype)) v))
      map_add' := by intros; simp
      map_smul' := by
        intro c v
        let f := (IntertwiningMap.equivAlgEnd (ρ.comp L.subtype)).symm c
        exact congrArg (Representation.asModuleEquiv (ρ.comp L.subtype)).symm
          (congrArg (fun A : Module.End (ZMod 2) V => A ((Representation.asModuleEquiv (ρ.comp L.subtype)) v)) (hg f)) }
    (by
      have hinv : Function.LeftInverse (ρ g⁻¹) (ρ g) := by intro v; simp
      have hrinv : Function.RightInverse (ρ g⁻¹) (ρ g) := by intro v; simp
      exact (Representation.asModuleEquiv (ρ.comp L.subtype)).symm.bijective.comp
        ((Function.bijective_iff_has_inverse.mpr ⟨ρ g⁻¹, hinv, hrinv⟩).comp
          (Representation.asModuleEquiv (ρ.comp L.subtype)).bijective))

/-- Scalar extension of the literal ambient actor through the published tensor identification. -/
noncomputable def tensorActor {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (g : G) (hg : Representation.IsSchurLinear ρ L g) :
    (Vector F ⊗[F] Vector F) ≃ₗ[F] (Vector F ⊗[F] Vector F) :=
  h.linearEquiv.symm.trans
    (((schurActor ρ L g hg).baseChange (SchurField (ρ.comp L.subtype)) F).trans h.linearEquiv)

theorem tensorActor_tmul {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (g : G) (hg : Representation.IsSchurLinear ρ L g)
    (a : F) (v : (Representation.asModule (ρ.comp L.subtype))) :
    tensorActor ρ L h g hg (h.linearEquiv (a ⊗ₜ v)) =
      h.linearEquiv (a ⊗ₜ (Representation.asModuleEquiv (ρ.comp L.subtype)).symm
        (ρ g ((Representation.asModuleEquiv (ρ.comp L.subtype)) v))) := by
  simp only [tensorActor, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.baseChange_tmul]
  rfl

variable [L.Normal]

/-- The extended operator induces the literal ambient conjugation automorphism. -/
theorem tensorActor_intertwines {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (g : G) (hg : Representation.IsSchurLinear ρ L g) (x : Sp F)
    (z : Vector F ⊗[F] Vector F) :
    tensorActor ρ L h g hg (twistedTensor h.sigma.toRingEquiv x z) =
      twistedTensor h.sigma.toRingEquiv (extensionAction L h.groupEquiv.symm g x)
        (tensorActor ρ L h g hg z) := by
  obtain ⟨z, rfl⟩ := h.linearEquiv.surjective z
  have hi (x : Sp F) (v) : twistedTensor h.sigma.toRingEquiv x (h.linearEquiv v) =
      h.linearEquiv (extendScalars F (Representation.endFieldRep (ρ.comp L.subtype)) (h.groupEquiv.symm x) v) := by
    simpa only [MulEquiv.apply_symm_apply] using (h.intertwines (h.groupEquiv.symm x) v).symm
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a v =>
    rw [hi, extendScalars_apply, LinearMap.baseChange_tmul, tensorActor_tmul,
      tensorActor_tmul, hi, extendScalars_apply, LinearMap.baseChange_tmul]
    congr 2
    simp only [endFieldRep_apply, LinearEquiv.apply_symm_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype, extensionAction_apply, map_mul, Module.End.mul_apply]
    simp

omit [L.Normal] in
/-- Pointwise fixing of the original displacement survives extension of scalars. -/
theorem tensorActor_fixes_displacement {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s) (j : L)
    (g : G) (hg : Representation.IsSchurLinear ρ L g)
    (hfix : ∀ v, ρ g (displacement ρ j.val v) = displacement ρ j.val v)
    (z : Vector F ⊗[F] Vector F) :
    tensorActor ρ L h g hg ((twistedTensor h.sigma.toRingEquiv (h.groupEquiv j) - (LinearMap.id : Module.End F (Vector F ⊗[F] Vector F))) z) =
      (twistedTensor h.sigma.toRingEquiv (h.groupEquiv j) - (LinearMap.id : Module.End F (Vector F ⊗[F] Vector F))) z := by
  obtain ⟨z, rfl⟩ := h.linearEquiv.surjective z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a v =>
    simp only [LinearMap.sub_apply, LinearMap.id_apply, ← h.intertwines,
      extendScalars_apply, LinearMap.baseChange_tmul, ← map_sub, ← TensorProduct.tmul_sub]
    rw [tensorActor_tmul]
    congr 2
    apply (Representation.asModuleEquiv (ρ.comp L.subtype)).injective
    simpa only [endFieldRep_apply, map_sub, LinearEquiv.apply_symm_apply,
      MonoidHom.comp_apply, Subgroup.coe_subtype, displacement, LinearMap.sub_apply,
      LinearMap.id_apply] using
      hfix ((Representation.asModuleEquiv (ρ.comp L.subtype)) v)

end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.AmbientContainment
