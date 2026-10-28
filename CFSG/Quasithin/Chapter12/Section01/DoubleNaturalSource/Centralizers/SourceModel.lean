module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Action
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceAdaptedPair
public import Theory.GroupTheory.SylowImageRestriction

/-!
# A compatible H.9 marking and its corrected adapted-pair application

`SourceModel` specifies compatibility of an H.9 source model with the
literal normalizer action quotient, the component quotient, and the two
supplied coordinate summands. Its construction remains an obligation;
none of its fields asserts an ambient centralizer or weak-closure conclusion.

Given this marking, H.9 supplies an inner conjugate of a nonsingular vector
and its actor. The component image lifts that conjugator to the original L.
The point-stabilizer preimage identity then lifts the stabilizer Sylow to
the original relative centralizer, with no assumption that the action kernel
is a two-group. The actor conclusion remains on its stated quotient image.

This is the corrected adapted marking used at the start of 12.1.1 and in
12.1.3, not the incompatible fixed-Sylow version of H.9.1(4).
Source: Aschbacher--Smith, printed pp.389,788--790; source-basis correction.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

/-- Action and marking compatibility, to be constructed from `DoubledBranch`. -/
structure SourceModel where
  setup : ChapterH.NaturalDual.SourceSetup n B.ActionQuotient
    (Additive (componentOrbit V (T : Subgroup G)))
  representation_eq : setup.representation = B.quotientRepresentation
  component_layer : B.componentToActionQuotient.range = componentLayer B.ActionQuotient
  layer_marking : ∀ l : L,
    setup.layer ⟨B.componentToActionQuotient l, component_layer ▸ ⟨l, rfl⟩⟩ =
      B.componentProjection l
  natural_marking : ∀ w : componentOrbit V (T : Subgroup G),
    Additive.ofMul w ∈ setup.natural ↔ (B.coordinates w).toAdd.2 = 0
  dual_marking : ∀ w : componentOrbit V (T : Subgroup G),
    Additive.ofMul w ∈ setup.dual ↔ (B.coordinates w).toAdd.1 = 0
  quadratic_eq : setup.quadratic = B.quadratic

namespace SourceModel
variable {B} (S : B.SourceModel)

theorem stabilizer_comap (w : componentOrbit V (T : Subgroup G)) :
    (S.setup.stabilizer (Additive.ofMul w)).comap B.actionProjection =
      (centralizer ({(w : G)} : Set G)).subgroupOf (normalizer (L : Set G)) := by
  rw [ChapterH.NaturalDual.SourceSetup.stabilizer, S.representation_eq]
  exact B.quotient_stabilizer_comap w

/-- Corrected H.9 on the original component and point-centralizer preimage. -/
theorem adapted_pair [Finite G]
    (P : Sylow 2 (normalizer (L : Set G)))
    (w : componentOrbit V (T : Subgroup G)) (hw : B.quadratic (Additive.ofMul w) = 1)
    (A : Subgroup (normalizer (L : Set G))) (hA : IsPGroup 2 A)
    (hAw : A ≤ (centralizer ({(w : G)} : Set G)).subgroupOf (normalizer (L : Set G))) :
    let Pbar := P.mapSurjective B.actionProjection_surjective
    ∃ l : L, ∃ w' : componentOrbit V (T : Subgroup G),
      (w' : G) = (l : G) * (w : G) * (l : G)⁻¹ ∧
      B.quadratic (Additive.ofMul w') = 1 ∧
      (∃ Q : Sylow 2 ((centralizer ({(w' : G)} : Set G)).subgroupOf (normalizer (L : Set G))),
        (Q : Subgroup _).map
          ((centralizer ({(w' : G)} : Set G)).subgroupOf (normalizer (L : Set G))).subtype =
          (P : Subgroup _) ⊓
            (centralizer ({(w' : G)} : Set G)).subgroupOf (normalizer (L : Set G))) ∧
      ((A.map B.actionProjection).map (MulAut.conj (B.componentToActionQuotient l)).toMonoidHom ≤
        (Pbar : Subgroup _) ⊓ S.setup.stabilizer (Additive.ofMul w')) ∧
      S.setup.moving (Additive.ofMul w') ⊓
        S.setup.fixed ((Pbar : Subgroup _) ⊓ S.setup.stabilizer (Additive.ofMul w')) =
          S.setup.fixed Pbar ∧
      Module.finrank (ZMod 2) (S.setup.fixed Pbar) = 1 ∧
      ∃ a ∈ S.setup.residual (Additive.ofMul w'),
        ∃ z ∈ S.setup.fixed Pbar, S.setup.representation a z ≠ z := by
  let Pbar := P.mapSurjective B.actionProjection_surjective
  have hAw' : A.map B.actionProjection ≤ S.setup.stabilizer (Additive.ofMul w) := by
    rw [map_le_iff_le_comap, S.stabilizer_comap]
    exact hAw
  obtain ⟨b, hb, v, hv, hq, ⟨Q, hQ⟩, hAQ, hfixed, hrank, hmoves⟩ :=
    S.setup.adapted_pair Pbar (Additive.ofMul w) (by rwa [S.quadratic_eq])
      (A.map B.actionProjection) (hA.map _) hAw'
  rw [← S.component_layer] at hb
  obtain ⟨l, hl⟩ := hb
  refine ⟨l, v.toMul, ?_, ?_, ?_, ?_, hfixed, hrank, hmoves⟩
  · rw [hv, S.representation_eq, ← hl]
    exact B.quotientAction_projection_apply (inclusion L.le_normalizer l) w
  · rwa [S.quadratic_eq] at hq
  · have ht := Subgroup.exists_sylow_preimage_inf_of_image P B.actionProjection
      B.actionProjection_surjective (S.setup.stabilizer v) Q hQ
    have hs := S.stabilizer_comap v.toMul
    simp only [ofMul_toMul] at hs
    rwa [hs] at ht
  · simpa only [hl, ofMul_toMul] using hAQ

end SourceModel
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
