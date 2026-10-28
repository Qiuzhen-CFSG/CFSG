module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesCubicConstituent

/-!
# The strict cubic bound on the same residual orbit quotient

The original Sylow diagram element descends through the orbit's kernel
quotient. The representative equation for the component equivalence keeps
its conjugation action and marking attached to the original projection.
The faithful quotient has trivial two-core, a normal PSL₃(4) component,
and a two-group quotient. The cubic constituent argument therefore gives
ratio greater than two on every previously chosen homogeneous orbit.

This discharges the PSL₃(4) D.3/B.4 obstruction in Aschbacher--Smith 5.1.23,
printed p.646, `refs/quasithin.pdf`. Construction of the small cubic bound
and exclusion of the alternative Suzuki component are separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open Representation.HermitianTensorThree.ImageOuter
open Matrix.PSL3.LinearThree.OuterExtensions
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
universe u v
variable {X : Type u} [Group X] [Finite X]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

omit [Finite X] [FiniteDimensional (ZMod 2) W] in
private theorem diagram_on_image
    {Y : Type*} [Group Y] (K J : Subgroup X) (hKJ : K ≤ J)
    (M : Subgroup Y) (q : J →* Y) (d : K ≃* M)
    (he : ∀ k : K, (d k : Y) = q (inclusion hKJ k))
    {F : Type*} [Field F] (e : K ≃* PSL(3,F))
    (t : X) (ht : t ∈ J) (a : MulAut K) (b : MulAut PSL(3,F))
    (ha : ∀ k : K, (a k : X) = t * k * t⁻¹)
    (hb : ∀ k, e (a k) = b (e k)) :
    ∃ (j : M ≃* PSL(3,F)) (a' : MulAut M),
      (∀ k : M, (a' k : Y) = q ⟨t,ht⟩ * k * (q ⟨t,ht⟩)⁻¹) ∧
      (∀ k : M, j (a' k) = b (j k)) := by
  let a' := MulAut.congr d a
  refine ⟨d.symm.trans e,a',?_,?_⟩
  · intro k
    obtain ⟨x,rfl⟩ := d.surjective k
    change (d (a (d.symm (d x))) : Y) = _
    rw [d.symm_apply_apply,he,he]
    have hx : inclusion hKJ (a x) =
        (⟨t,ht⟩ : J) * inclusion hKJ x * (⟨t,ht⟩ : J)⁻¹ := Subtype.ext (ha x)
    rw [hx,map_mul,map_mul,map_inv]
  · intro k
    change e (d.symm (d (a (d.symm k)))) = b (e (d.symm k))
    rw [d.symm_apply_apply]
    exact hb (d.symm k)

/-- The original diagram element excludes a small cubic ratio on every
previously selected homogeneous orbit's literal faithful quotient. -/
theorem residual_orbit_cubicRatio_gt_two
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X) [K.Normal]
    (hm : ClassicalGroup.IsPSL K 3 4) (hP : IsPGroup 2 P)
    (κ : GroupClass.{u}) (hsq : IsSQTK κ K) (hkg : IsKGroup κ X)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : K ≃* PSL(3,F)) (t : X) (ht : t ∈ P)
    (a : MulAut K) (b : MulAut PSL(3,F))
    (ha : ∀ k : K, (a k : X) = t * k * t⁻¹)
    (hb : ∀ k, e (a k) = b (e k)) (hd : b ∉ diagramTrivial F)
    {I : Submodule (ZMod 2) W} (hI : IsIrrPlusWith ρ K P I) :
    2 < cubicRatio (KernelQuotient.action (orbitSectionRepresentation ρ hI)) := by
  let J := K ⊔ P
  let K₀ := K.subgroupOf J
  let σ := orbitSectionRepresentation ρ hI
  let q := KernelQuotient.projection σ
  let M := K₀.map q
  let : K₀.Normal := inferInstanceAs ((K.subgroupOf J).Normal)
  let : M.Normal := (inferInstance : K₀.Normal).map q
    (KernelQuotient.projection_surjective σ)
  have hgen : K₀ ⊔ P.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show K ≤ J from le_sup_left)
      (show P ≤ J from le_sup_right)]
    exact subgroupOf_self _
  have hquot : IsPGroup 2 (J ⧸ K₀) :=
    quotient_isPGroup_of_sup_eq_top (P.subgroupOf J) K₀ hP.comap_subtype
      ((sup_comm _ _).trans hgen)
  have hquot' : IsPGroup 2 (KernelQuotient.Actor σ ⧸ M) :=
    hquot.of_surjective (QuotientGroup.map K₀ M q (le_comap_map q K₀))
      (QuotientGroup.map_surjective_of_surjective K₀ M q
        ((QuotientGroup.mk'_surjective M).comp (KernelQuotient.projection_surjective σ))
        (le_comap_map q K₀))
  obtain ⟨hqs,hz,_⟩ := ChapterK.Linear.Recognition.PSL3FourExclusion.model_facts hm
  let := hqs
  let d : K ≃* M := orbitSectionComponentEquiv ρ hz hI
  have he (k : K) : (d k : KernelQuotient.Actor σ) =
      q (inclusion (show K ≤ J from le_sup_left) k) :=
    orbitSectionComponentEquiv_apply ρ hz hI k
  obtain ⟨j,a',ha',hb'⟩ := diagram_on_image K J le_sup_left M q d he
    e t (mem_sup_right ht) a b ha hb
  exact cubicRatio_gt_two_of_diagram (KernelQuotient.action σ) M κ
    (residual_orbit_sqtk ρ K P hm hP κ hsq hkg hI)
    (residual_orbit_structure ρ K P hm hP hI).2.2 hquot'
    (orbitSection_faithful_twoCore_eq_bot ρ hz hP hI) (KernelQuotient.faithful σ)
    hF j (q ⟨t,mem_sup_right ht⟩) a' b ha' hb' hd

/-- The bound on every specified seed, before specializing the nested action. -/
@[expose] def ResidualOrbitCubicBound
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X) : Prop :=
  ∀ (I : Submodule (ZMod 2) W) (hI : IsIrrPlusWith ρ K P I),
    2 < cubicRatio (KernelQuotient.action (orbitSectionRepresentation ρ hI))

theorem residual_orbit_cubic_bound
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X) [K.Normal]
    (hm : ClassicalGroup.IsPSL K 3 4) (hP : IsPGroup 2 P)
    (κ : GroupClass.{u}) (hsq : IsSQTK κ K) (hkg : IsKGroup κ X)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : K ≃* PSL(3,F)) (t : X) (ht : t ∈ P)
    (a : MulAut K) (b : MulAut PSL(3,F))
    (ha : ∀ k : K, (a k : X) = t * k * t⁻¹)
    (hb : ∀ k, e (a k) = b (e k)) (hd : b ∉ diagramTrivial F) :
    ResidualOrbitCubicBound ρ K P := by
  intro I hI
  exact residual_orbit_cubicRatio_gt_two ρ K P hm hP κ hsq hkg hF e t ht a b ha hb hd hI

/-- A constructed orbit with its original moved space, faithful component,
and strict cubic bound on the faithful central quotient. -/
@[expose] def HasStrictResidualOrbit
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X) : Prop :=
  ∃ (I : Submodule (ZMod 2) W) (hI : IsIrrPlusWith ρ K P I),
    let σ := orbitSectionRepresentation ρ hI
    subspaceCommutator ρ (orbitSpan ρ P I) K = orbitSpan ρ P I ∧
      Function.Injective (σ.comp (inclusion (show K ≤ K ⊔ P from le_sup_left))) ∧
      2 < cubicRatio (KernelQuotient.action σ)

omit [Finite X] [FiniteDimensional (ZMod 2) W] in
/-- Keep the already supplied orbit witness and add its proved cubic bound. -/
theorem strict_residual_orbit
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X)
    (hs : HasFaithfulHomogeneousOrbitSection ρ K P)
    (hb : ResidualOrbitCubicBound ρ K P) : HasStrictResidualOrbit ρ K P := by
  obtain ⟨I,hI,hm,hf⟩ := hs
  exact ⟨I,hI,hm,hf,hb I hI⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
