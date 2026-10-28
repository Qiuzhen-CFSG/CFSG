module
public import Theory.Representation.BinaryOffender.MarkedOrbitCore
public import Theory.Representation.BinaryOffender.NormalOddSeed
public import Mathlib.LinearAlgebra.Projection

/-!
# Projected Sylow-fixed generating seeds

A surjective equivariant linear map sends a Sylow-fixed seed to a fixed seed
whose ambient orbit still spans. Passing to the faithful image and applying
`MarkedOrbitCore` therefore excludes its normal two-core. The actor surjection
and linear projection remain literal throughout.

For complementary invariant summands, the complementary projection is
equivariant. The coprime fixed/moved splitting for a normal odd subgroup then
supplies the residual C_V(Y) action and its trivial two-core. The quotient
consumer uses the actual subrepresentation quotient map. No full-movement
hypothesis or condition on the original action kernel is required.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, original
15.1.2, first paragraph, printed pp.1084–1085, and its D.2.17 reduction.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
  (f : G →* D) (e : V →ₗ[ZMod 2] W)
  (hact : ∀ g v, e (ρ g v) = σ (f g) (e v))

include hact in
theorem fixed_seed_map (S : Subgroup G) (Z : Submodule (ZMod 2) V)
    (hfix : Z ≤ fixedSpace ρ S) : Z.map e ≤ fixedSpace σ (S.map f) := by
  rintro _ ⟨v,hv,rfl⟩ ⟨_,g,hg,rfl⟩
  change σ (f g) (e v) = e v
  rw [← hact,show ρ g v = v from hfix hv ⟨g,hg⟩]

include hact in
theorem orbit_seed_map (he : Function.Surjective e) (Z : Submodule (ZMod 2) V)
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤) :
    Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z.map e ∧ σ g v = w} = ⊤ := by
  apply top_unique
  intro w _
  obtain ⟨v,rfl⟩ := he w
  have hv : v ∈ Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} :=
    hspan ▸ Submodule.mem_top
  have hm : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} ≤
      (Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z.map e ∧ σ g v = w}).comap e := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,z,hz,rfl⟩
    change e (ρ g z) ∈ Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z.map e ∧ σ g v = w}
    rw [hact]
    exact Submodule.subset_span ⟨f g,e z,⟨z,hz,rfl⟩,rfl⟩
  exact hm hv

include hact in
theorem projected_seed_twoCore [Finite G] (hf : Function.Surjective f) (he : Function.Surjective e)
    (hfaith : Function.Injective σ) (S : Sylow 2 G) (Z : Submodule (ZMod 2) V)
    (hfix : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤) :
    pCore 2 D = ⊥ :=
  twoCore_eq_bot_of_sylow_fixed_span σ hfaith (S.mapSurjective hf) (Z.map e)
    (fixed_seed_map ρ σ f e hact S Z hfix) (orbit_seed_map ρ σ f e hact he Z hspan)

variable {ρ σ f e}
theorem projected_actionImage_twoCore [Finite G]
    (σ : Representation (ZMod 2) G W) (e : V →ₗ[ZMod 2] W)
    (hact : ∀ g v, e (ρ g v) = σ g (e v)) (he : Function.Surjective e)
    (S : Sylow 2 G) (Z : Submodule (ZMod 2) V)
    (hfix : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤) :
    pCore 2 (actionImage σ) = ⊥ := by
  apply projected_seed_twoCore ρ (imageRepresentation σ) (actionHom σ) e hact
    σ.asGroupHom.rangeRestrict_surjective he (imageRepresentation_injective σ) S Z hfix hspan

section Projection
variable (ρ) (U R : Submodule (ZMod 2) V)
  (hU : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ U)
  (hR : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ R) (hcompl : IsCompl U R)

include hR in
theorem complementProjection_intertwines (g : G) (v : V) :
    U.projectionOnto R hcompl (ρ g v) =
      subspaceImageRepresentation ρ U (invariantActionHom ρ U hU g)
        (U.projectionOnto R hcompl v) := by
  obtain ⟨u,hu,r,hr,rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ U ⊔ R from hcompl.sup_eq_top ▸ Submodule.mem_top)
  have hgu : ρ g u ∈ U := (hU (mem_top g) u).2 hu
  have hgr : ρ g r ∈ R := (hR (mem_top g) r).2 hr
  simp only [map_add,Submodule.projectionOnto_apply_of_mem_left hcompl hu,
    Submodule.projectionOnto_apply_of_mem_left hcompl hgu,
    Submodule.projectionOnto_apply_of_mem_right hcompl hr,
    Submodule.projectionOnto_apply_of_mem_right hcompl hgr,add_zero]
  rfl

theorem complementProjection_surjective : Function.Surjective (U.projectionOnto R hcompl) :=
  fun u => ⟨u,Submodule.projectionOnto_apply_left hcompl u⟩

include hU hR hcompl in
theorem complementImage_twoCore [Finite G] (S : Sylow 2 G) (Z : Submodule (ZMod 2) V)
    (hfix : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤) :
    pCore 2 (subspaceActionImage ρ U) = ⊥ :=
  projected_seed_twoCore ρ (subspaceImageRepresentation ρ U) (invariantActionHom ρ U hU)
    (U.projectionOnto R hcompl) (complementProjection_intertwines ρ U R hU hR hcompl)
    (invariantActionHom_surjective ρ U hU) (complementProjection_surjective U R hcompl)
    (subspaceImageRepresentation_injective ρ U) S Z hfix hspan
end Projection

variable (ρ)
/-- The faithful residual action on C_V(Y) retains a projected Sylow-fixed
orbit-generating seed; its two-core is therefore trivial. -/
theorem normalOddFixedImage_twoCore [Finite G] (Y : Subgroup G) [Y.Normal]
    (hodd : Odd (Nat.card Y)) (S : Sylow 2 G) (Z : Submodule (ZMod 2) V)
    (hfix : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤) :
    pCore 2 (subspaceActionImage ρ (fixedSpace ρ Y)) = ⊥ := by
  have hc : IsCompl (fixedSpace ρ Y) (subspaceCommutator ρ ⊤ Y) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hodd)
  have hm : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ Y) :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) le_normalizer_of_normal
  exact complementImage_twoCore ρ _ _ (fixedSpace_stable_of_normal ρ Y) hm hc S Z hfix hspan

/-- The literal quotient map retains the generating marker. -/
theorem quotientImage_twoCore [Finite G] (N : Subrepresentation ρ)
    (S : Sylow 2 G) (Z : Submodule (ZMod 2) V)
    (hfix : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤) :
    pCore 2 (actionImage N.quotientRepresentation) = ⊥ :=
  projected_actionImage_twoCore N.quotientRepresentation N.toSubmodule.mkQ
    (fun _ _ => rfl) N.toSubmodule.mkQ_surjective S Z hfix hspan

end Representation.BinaryOffender
