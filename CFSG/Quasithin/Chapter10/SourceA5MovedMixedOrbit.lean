module
public import CFSG.Quasithin.Chapter10.SourceA5MovedSeedTypes
public import Theory.Representation.AlternatingFiveMovedPair.MixedTypes
public import Theory.Representation.BinaryOffender.Homogeneous.QuotientOrbitModels
public import CFSG.Quasithin.Chapter10.SourceA5LocalCentralQuotient.OrbitComparison
/-!
# The mixed pair on the original local central quotient

A proper homogeneous seed of either mixed A₅-product type generates the full
mixed pair in its central orbit. The two possible automorphism types and
homogeneity identify the orbit span with the direct product, and the original
quotient coordinates transport this model to the literal local actor.

Both factors retain one common marking A₅ ≃ SL₂(4). If the initial seed has
the reversed mixed type, the product commutor restores the exact summand
order in `AlternatingFiveMovedPair.Mixed.action`.

Source: Aschbacher–Smith, D.3.5, printed pp. 195–196.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
open Representation.AlternatingFiveMovedPair
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))

/-- The actual central orbit of the original homogeneous seed. -/
abbrev originalSeedCentralSpan :=
  (centralTypeAction (ReducedNormal.representation (localJoin T L))
    ((localOrbit T L).subgroupOf (localJoin T L))
    ((T : Subgroup G).subgroupOf (localJoin T L)) D.homogeneous.normalizes).span
      (originalSeedCentralImage D)

private def originalSeedModelInflation {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) W)
    (b : (originalA5SeedAction D e hn ht htn).Equiv τ) :
    (originalSeedCentralImage D).toRepresentation.Equiv
      (τ.comp ((originalSeedProductQuotient D e hn ht htn).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 ((localOrbit T L).subgroupOf (localJoin T L)))))) :=
  Representation.Equiv.mk b.toLinearEquiv (by
    intro x
    apply LinearMap.ext
    intro v
    have he := Representation.IntertwiningMap.isIntertwining
      (originalA5SeedAction D e hn ht htn) τ b.toIntertwiningMap
        (originalSeedProductQuotient D e hn ht htn (QuotientGroup.mk' _ x)) v
    rw [originalSeedProductQuotient_apply, originalA5SeedAction_apply] at he
    exact he)

/-- Either original mixed seed orientation generates the exact complete mixed pair. -/
theorem source_a5_moved_mixed_central_span
    (hproper : D.seed ≠ D.moduleSubgroup)
    (base : alternatingGroup (Fin 5) ≃* SL2FourNatural.SL)
    (hseed : Nonempty ((originalA5SeedAction D e hn ht htn).Equiv
        (MixedTypes.firstSL.comp (base.prodCongr base).toMonoidHom)) ∨
      Nonempty ((originalA5SeedAction D e hn ht htn).Equiv
        (MixedTypes.secondSL.comp (base.prodCongr base).toMonoidHom))) :
    Nonempty ((originalSeedCentralSpan D).toRepresentation.Equiv
      ((Mixed.action.comp (base.prodCongr base).toMonoidHom).comp
        ((originalSeedProductQuotient D e hn ht htn).toMonoidHom.comp
          (QuotientGroup.mk' (pCore 2 ((localOrbit T L).subgroupOf (localJoin T L))))))) := by
  let ρ := ReducedNormal.representation (localJoin T L)
  let X := (localOrbit T L).subgroupOf (localJoin T L)
  let S := (T : Subgroup G).subgroupOf (localJoin T L)
  let N := pCore 2 X
  let q := originalSeedProductQuotient D e hn ht htn
  let f := q.toMonoidHom.comp (QuotientGroup.mk' N)
  let τ₀ := MixedTypes.firstSL.comp (base.prodCongr base).toMonoidHom
  let τ₁ := MixedTypes.secondSL.comp (base.prodCongr base).toMonoidHom
  have hmoved : orbitSpan ρ S D.seedSpace ≠ D.seedSpace := by
    intro he
    apply hproper
    rw [D.module_eq_subspaceImage, he]
    rfl
  rcases hseed with hb | hb
  · obtain ⟨b⟩ := hb
    obtain ⟨a⟩ := D.homogeneous.central_span_equiv_pair ρ N q τ₀ τ₁
      (originalSeedModelInflation D e hn ht htn τ₀ b) hmoved (by
        intro a
        rcases MixedTypes.marked_model_automorphism_types base a with h | h
        · exact Or.inl h.1
        · exact Or.inr h.1)
    exact ⟨a⟩
  · obtain ⟨b⟩ := hb
    obtain ⟨a⟩ := D.homogeneous.central_span_equiv_pair ρ N q τ₁ τ₀
      (originalSeedModelInflation D e hn ht htn τ₁ b) hmoved (by
        intro a
        rcases MixedTypes.marked_model_automorphism_types base a with h | h
        · exact Or.inl h.2
        · exact Or.inr h.2)
    let c : Representation.Equiv ((Representation.prod τ₁ τ₀).comp f)
        ((Representation.prod τ₀ τ₁).comp f) :=
      Representation.Equiv.mk (LinearEquiv.prodComm (ZMod 2) _ _) (by
        intro x
        apply LinearMap.ext
        intro v
        rfl)
    exact ⟨a.trans c⟩

/-- The actual Sylow orbit image has the complete mixed pair model. -/
theorem source_a5_moved_mixed_orbit_image
    (hproper : D.seed ≠ D.moduleSubgroup)
    (base : alternatingGroup (Fin 5) ≃* SL2FourNatural.SL)
    (hseed : Nonempty ((originalA5SeedAction D e hn ht htn).Equiv
        (MixedTypes.firstSL.comp (base.prodCongr base).toMonoidHom)) ∨
      Nonempty ((originalA5SeedAction D e hn ht htn).Equiv
        (MixedTypes.secondSL.comp (base.prodCongr base).toMonoidHom))) :
    Nonempty ((sourceLocalOrbitImage D).toRepresentation.Equiv
      ((Mixed.action.comp (base.prodCongr base).toMonoidHom).comp
        ((originalSeedProductQuotient D e hn ht htn).toMonoidHom.comp
          (QuotientGroup.mk' (pCore 2 ((localOrbit T L).subgroupOf (localJoin T L))))))) := by
  have he : sourceLocalOrbitImage D = originalSeedCentralSpan D := by
    apply Subrepresentation.toSubmodule_injective
    rw [source_local_orbit_image_eq_centralOrbitSpan]
    exact (centralTypeAction_span _ _ _ _ _).symm
  rw [he]
  exact source_a5_moved_mixed_central_span D e hn ht htn hproper base hseed

local instance localMixedElementary : IsElementaryAbelian 2 D.moduleSubgroup := D.module_elementary

/-- Under the literal original A₅ pair embedding, the faithful local quotient
has the complete mixed pair model with the same shared baseline. -/
theorem source_a5_moved_mixed_local_quotient
    (hproper : D.seed ≠ D.moduleSubgroup)
    (base : alternatingGroup (Fin 5) ≃* SL2FourNatural.SL)
    (hseed : Nonempty ((originalA5SeedAction D e hn ht htn).Equiv
        (MixedTypes.firstSL.comp (base.prodCongr base).toMonoidHom)) ∨
      Nonempty ((originalA5SeedAction D e hn ht htn).Equiv
        (MixedTypes.secondSL.comp (base.prodCongr base).toMonoidHom))) :
    let U := D.moduleSubgroup.subgroupOf (localJoin T L)
    let := (source_parabolic_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set (localJoin T L)))
    ∀ (τ : Representation (ZMod 2)
        ((localJoin T L) ⧸ centralizer (U : Set (localJoin T L)))
        (Additive (sourceLocalCentralQuotient D)))
      (i : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →*
        ((localJoin T L) ⧸ centralizer (U : Set (localJoin T L)))),
      (∀ x : localOrbit T L,
        i (originalA5ProductProjection D e hn ht htn x) =
          q (inclusion (show localOrbit T L ≤ localJoin T L from le_sup_left) x)) →
      (∀ (m : localJoin T L) (v : D.moduleSubgroup),
        τ (q m) (Additive.ofMul (QuotientGroup.mk' (sourceLocalCentralizer D) v)) =
          Additive.ofMul (QuotientGroup.mk' (sourceLocalCentralizer D)
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.join_normalizes_module m.property) v).mp
                v.property⟩)) →
      Nonempty (Representation.Equiv (τ.comp i)
        (Mixed.action.comp (base.prodCongr base).toMonoidHom)) := by
  dsimp only
  let := (source_parabolic_module_reduced D).normal
  intro τ i hi hτ
  obtain ⟨a, _⟩ := source_local_quotient_orbit_image_equiv D τ hτ
  obtain ⟨b⟩ := source_a5_moved_mixed_orbit_image D e hn ht htn hproper base hseed
  let c := a.symm.trans b
  refine ⟨Representation.Equiv.mk c.toLinearEquiv ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  obtain ⟨x, rfl⟩ := originalA5ProductProjection_surjective D e hn ht htn g
  let xX : (localOrbit T L).subgroupOf (localJoin T L) :=
    ⟨inclusion (show localOrbit T L ≤ localJoin T L from le_sup_left) x, x.property⟩
  have hc := Representation.IntertwiningMap.isIntertwining _ _ c.toIntertwiningMap xX v
  change c (τ (i (originalA5ProductProjection D e hn ht htn x)) v) =
    Mixed.action ((base.prodCongr base) (originalA5ProductProjection D e hn ht htn x)) (c v)
  rw [hi x]
  exact hc

end CFSG.Quasithin.Chapter10
