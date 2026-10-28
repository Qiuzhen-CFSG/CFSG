module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.ModelClassification.ScalarComparison


/-!
# Binary nine-dimensional modules of the native M22 point stabilizer

Inflate an arbitrary simple binary module through the actual marked central
quotient of SL₃(4). Its Schur-field catalogue forces degree one and one of
the two constant tensor words. The Hermitian scalar-extension comparisons
identify those words with the two fixed concrete models, and Noether–Deuring
descends the actual intertwiner. Surjectivity of the original quotient then
returns the equivalence to the literal point stabilizer.

No faithfulness, absolute irreducibility, or complete reducibility is assumed.
This supplies the model comparison used by the nine-submodule induction branch
for Guralnick–Malle I, Proposition 5.1, pp.15–16. The Hermitian construction
is Aschbacher–Smith H.4.2–4, printed pp.380–381.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule
open ModelClassification

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- Every irreducible binary module of dimension nine for the native point
stabilizer is one of the actual Hermitian model and its contragredient. -/
theorem exists_point_model_equiv
    (τ : Representation (ZMod 2) Models.pointGroup W) [τ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) W = 9) :
    ∃ b : Bool, Nonempty (τ.Equiv (Models.pointAction b)) := by
  let q := QuotientGroup.mk' (Subgroup.center Matrix.PSL3Four.SL)
  let p := MathieuCode.m22PointStabilizerEquiv 0
  let h : Matrix.PSL3Four.SL →* Models.pointGroup := p.symm.toMonoidHom.comp q
  have hsurj : Function.Surjective h :=
    p.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  let σ : Representation (ZMod 2) Matrix.PSL3Four.SL W := τ.comp h
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff h hsurj τ).mpr inferInstance
  let : Algebra (ZMod 2) (SplittingField σ) := ZMod.algebra _ 2
  obtain ⟨ι, b, ⟨e⟩⟩ := original_absolute_word σ hd
  obtain ⟨m⟩ := model_extension ι b
  obtain ⟨d⟩ := BinaryFieldDescent.equiv_of_extendScalars
    (K := SplittingField σ) σ ((Models.projective b).comp q) ⟨e.trans m.symm⟩
  refine ⟨b, ⟨.mk d.toLinearEquiv ?_⟩⟩
  intro g
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center Matrix.PSL3Four.SL) (p g)
  ext v
  have he := LinearMap.congr_fun (d.isIntertwining' a) v
  change d (τ (p.symm (q a)) v) = Models.projective b (q a) (d v) at he
  change d (τ g v) = Models.projective b (p g) (d v)
  change q a = p g at ha
  rw [ha, p.symm_apply_apply] at he
  exact he

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule
