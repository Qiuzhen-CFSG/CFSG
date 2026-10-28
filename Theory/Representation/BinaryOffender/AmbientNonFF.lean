module
public import Theory.Representation.BinaryOffender.HomogeneousOrbitAction
public import Theory.Representation.BinaryOffender.Restriction
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import Theory.Representation.BinaryOffender.FaithfulInvariantSection
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent

/-!
# From a non-FF component section to the ambient action

A best offender preserving a subspace fixes it pointwise if its restricted
image is non-FF. If a component acts faithfully there, the offender then
centralizes that component. Conjugation through a Sylow subgroup makes
such an offender centralize the whole component orbit. When that orbit
contains the two-residual and the two-core is trivial, generalized Fitting
self-centralization excludes the offender.

The homogeneous-orbit specialization retains the entire central cover.
The original terminal action is the consumer in Chapter14's
ComponentSupports.Modules.Recognition.AmbientNonFF.
Source: Aschbacher--Smith B.1.5(4), B.5.6 and14.6.22--24,
printed pp.71,103,1038--1039.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
open Homogeneous
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- A best offender acts trivially on an invariant subspace whose full
restricted actor image is non-FF. -/
theorem IsBestOffender.fixed_of_nonFF_invariant_image
    {A J : Subgroup G} (hA : IsBestOffender ρ A) (hAJ : A ≤ J)
    (W : Submodule (ZMod 2) V) (hW : J ≤ subspaceStabilizer ρ W)
    (hn : ¬ IsFFModule (imageRepresentation (invariantSubspace ρ J W hW).toRepresentation)) :
    W ≤ fixedSpace ρ A := by
  let σ := ρ.comp J.subtype
  let τ := (invariantSubspace ρ J W hW).toRepresentation
  have hs : (⊤ : Subgroup J) ≤ subspaceStabilizer σ W := fun g _ => hW g.property
  have hfix : W ≤ fixedSpace σ (A.subgroupOf J) := by
    by_contra hfix
    have hb := (hA.subgroupOf ρ hAJ).restricted σ W (le_top.trans hs) hfix
    let f : J →* subspaceStabilizer σ W := {
      toFun g := ⟨g,hs (mem_top g)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hf : Function.Surjective f := fun g => ⟨g.val,Subtype.ext rfl⟩
    exact hn (image_isFFModule_of_equivariant τ (stabilizerRepresentation σ W)
      f hf (LinearEquiv.refl _ _) (fun _ _ => rfl)
      ⟨_,hb.isOffender _⟩)
  rwa [fixedSpace_subgroupOf ρ A J hAJ] at hfix

/-- A best offender normalizing a centerless component centralizes it
when the image on its full homogeneous orbit is non-FF. -/
theorem IsBestOffender.centralizes_of_nonFF_orbit
    {K P A : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    (hP : IsPGroup 2 P) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) (hA : IsBestOffender ρ A) (hAP : A ≤ P)
    (hn : ¬ IsFFModule (imageRepresentation
      (invariantSubspace ρ (K ⊔ P) (orbitSpan ρ P I)
        (sup_le (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)
          (orbitSpan_invariant ρ P I))).toRepresentation)) :
    A ≤ centralizer (K : Set G) := by
  let O := orbitSpan ρ P I
  have hO := orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus
  have hfix := hA.fixed_of_nonFF_invariant_image ρ
    (hAP.trans (show P ≤ K ⊔ P from le_sup_right)) O
    (sup_le hO (orbitSpan_invariant ρ P I)) hn
  have hf := orbit_component_faithful ρ hz hP hI
  intro a ha
  apply centralizes_of_fixes_faithful_section ρ K O hO
    (fun k hk h => ?_) (hI.normalizes (hAP ha)) (fun v hv => hfix hv ⟨a,ha⟩)
  have he : (invariantSubspace ρ K O hO).toRepresentation ⟨k,hk⟩ = 1 := by
    ext v
    exact h v v.property
  exact congrArg Subtype.val ((injective_iff_map_eq_one _).mp hf ⟨k,hk⟩ he)

/-- Centralization of one component by all Sylow best offenders excludes
FF when its Sylow orbit contains the two-residual and the two-core is trivial. -/
theorem not_ff_of_sylow_best_centralizes_orbit
    (S : Sylow 2 G) (K : Subgroup G) (hcore : pCore 2 G = ⊥)
    (hres : pResidual 2 G ≤ componentOrbit K (S : Subgroup G))
    (hc : ∀ A : Subgroup G, A ≤ S → IsBestOffender ρ A →
      A ≤ centralizer (K : Set G)) : ¬ IsFFModule ρ := by
  intro hff
  obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
  obtain ⟨Q,hQ⟩ := hA.1.2.isPGroup.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G Q S
  let B := A.map (MulAut.conj g).toMonoidHom
  have hB := hA.map_conj ρ g
  have hBS : B ≤ S := by
    rw [←hg]
    exact map_mono hQ
  have hBC : B ≤ centralizer (componentOrbit K (S : Subgroup G) : Set G) := by
    apply le_centralizer_iff.mpr
    apply iSup_le
    intro t
    apply le_centralizer_iff.mp
    intro b hb x hx
    obtain ⟨k,hk,rfl⟩ := hx
    have hbt : t.val⁻¹*b*t.val ∈ B.map (MulAut.conj t.val⁻¹).toMonoidHom :=
      by simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
        (mem_map_of_mem (MulAut.conj t.val⁻¹).toMonoidHom hb)
    have hbtS : B.map (MulAut.conj t.val⁻¹).toMonoidHom ≤ S := by
      rintro _ ⟨b,hb,rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
        S.mul_mem (S.mul_mem (S.inv_mem t.property) (hBS hb)) t.property
    have hh := hc _ hbtS (hB.map_conj ρ t.val⁻¹) hbt k hk
    have he := congrArg (MulAut.conj t.val) hh
    simpa only [map_mul,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,
      mul_assoc,mul_inv_cancel_left,inv_mul_cancel_left,mul_inv_cancel,inv_mul_cancel,
      mul_one,one_mul] using he
  have hBF : B ≤ fittingSubgroup G :=
    (hBC.trans (centralizer_le hres)).trans
      ((centralizer_le (generalizedFitting_le_pResidual_of_pCore_eq_bot hcore)).trans
        centralizer_generalizedFitting_le_fitting)
  exact hB.1.1 (le_bot_iff.mp
    ((le_pCore_of_le_fitting B (hB.1.2.isPGroup 2 B) hBF).trans hcore.le))
end Representation.BinaryOffender
