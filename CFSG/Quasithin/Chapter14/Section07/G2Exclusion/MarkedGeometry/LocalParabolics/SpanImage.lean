module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.ConjugateCoverage
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.Saturation
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.FamilyAction
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import Theory.GroupAction.ExtendingSubgroupAutomorphisms
public import Theory.GroupTheory.PCoreImage

/-!
# The full binary span stabilizer

Write `W = U(V₂) = ⟨V^Y⟩` for the literal span supplied by the marked
pencil.  The action of the local vertex `N_G(V₂)` on `W` is the actual
conjugation action, and `P` is the stabilizer of the marked four-group
`V₂.subgroupOf W` in `Aut(W)`.

The source calculation has four separate ingredients.  The 14.7.55 module
calculation gives the one-sided cover `P ≤ P₀ O₂(P)`, the image of `Y`
has a nontrivial two-core, and the action on `O₂(P)` is irreducible.  The
normality of `Y` in the local vertex gives the containment of the two-core of
its image.  This file derives the equality `P = P₀ O₂(P)`, the containment
and nontriviality premises, and the abelian-radical centralizer premise before
using the abstract saturation lemma.  Thus surjectivity onto the two binary
factors is not used: the whole stabilizer is obtained.

The local vertex `G₂ = N_G(V₂)` here is an ambient vertex stabilizer; it is
unrelated to the Lie group `G₂(2)` used for the quotient model.  All subgroup
maps below are literal maps on `W`, and relative normality is retained.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
Lemma 14.7.56(2), printed p.1066 (PDF p.1083), using 14.7.55 and the
actual natural/Weyl model action.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics

open Subgroup
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
open scoped Pointwise

variable {G : Type*} [Group G]

/-- The literal ambient action on the span preserves the marked four-group.
This is the setwise stabilizer inclusion used before applying the source
factorization. -/
theorem ambient_span_action_range_le_stabilizer
    (V V₂ Y : Subgroup G) (hV₂ : V₂ ≤ V)
    (hspan : normalizer (V₂ : Set G) ≤
      normalizer (generatedLineFamily V Y : Set G)) :
    let W := generatedLineFamily V Y
    let ρ := @ambientAction G _ (normalizer (V₂ : Set G)) W hspan
    ρ.range ≤ MulAction.stabilizer (MulAut W) (V₂.subgroupOf W) := by
  dsimp only
  let W := generatedLineFamily V Y
  let N := normalizer (V₂ : Set G)
  let ρ := @ambientAction G _ N W hspan
  have hV₂W : V₂ ≤ W := hV₂.trans (original_le_generated V Y)
  intro a ha
  obtain ⟨n, rfl⟩ := ha
  apply (mem_automorphism_stabilizer_iff (V₂.subgroupOf W) _).mpr
  intro w
  change ρ n w ∈ V₂.subgroupOf W ↔ w ∈ V₂.subgroupOf W
  change (ρ n w : G) ∈ V₂ ↔ (w : G) ∈ V₂
  change (W.normalizerMonoidHom (inclusion hspan n) w : G) ∈ V₂ ↔
    (w : G) ∈ V₂
  rw [normalizerMonoidHom_apply_apply_coe]
  change (n : G) * (w : G) * (n : G)⁻¹ ∈ V₂ ↔ (w : G) ∈ V₂
  exact (mem_normalizer_iff.mp n.property (w : G)).symm

/-- The image of the `Y` action is a literal subgroup of the local-vertex
image.  This is the map-level comparison needed for the relative core lemma. -/
theorem local_residual_action_range_le_vertex_action_range
    (V V₂ Y : Subgroup G)
    (hYV : Y ≤ normalizer (V₂ : Set G))
    (hspan : normalizer (V₂ : Set G) ≤
      normalizer (generatedLineFamily V Y : Set G)) :
    let W := generatedLineFamily V Y
    let ρ := @ambientAction G _ (normalizer (V₂ : Set G)) W hspan
    let σ := @ambientAction G _ Y W (hYV.trans hspan)
    σ.range ≤ ρ.range := by
  dsimp only
  let W := generatedLineFamily V Y
  let N := normalizer (V₂ : Set G)
  let ρ := @ambientAction G _ N W hspan
  let σ := @ambientAction G _ Y W (hYV.trans hspan)
  rintro a ⟨y, rfl⟩
  refine ⟨⟨(y : G), hYV y.property⟩, ?_⟩
  rfl

/-- Normality of the residual image promotes its two-core into the vertex
image's two-core.  The hypothesis is the actual source normality statement
transported through the two conjugation actions. -/
theorem local_residual_two_core_le_vertex_two_core
    (V V₂ Y : Subgroup G) (hYV : Y ≤ normalizer (V₂ : Set G))
    (hspan : normalizer (V₂ : Set G) ≤
      normalizer (generatedLineFamily V Y : Set G))
    (hnormal :
      let W := generatedLineFamily V Y
      let ρ := @ambientAction G _ (normalizer (V₂ : Set G)) W hspan
      let σ := @ambientAction G _ Y W (hYV.trans hspan)
      ρ.range ≤ normalizer (σ.range : Set (MulAut W))) :
    let W := generatedLineFamily V Y
    let ρ := @ambientAction G _ (normalizer (V₂ : Set G)) W hspan
    let σ := @ambientAction G _ Y W (hYV.trans hspan)
    σ.range.pCoreIn 2 ≤ ρ.range.pCoreIn 2 := by
  dsimp only at hnormal ⊢
  let W := generatedLineFamily V Y
  let N := normalizer (V₂ : Set G)
  let ρ := @ambientAction G _ N W hspan
  let σ := @ambientAction G _ Y W (hYV.trans hspan)
  apply pCoreIn_mono_of_normalizes
    (local_residual_action_range_le_vertex_action_range V V₂ Y hYV hspan)
  exact hnormal

/-- Commutativity of the source radical is converted to the centralizer
hypothesis required by saturation.  The source's elementary-abelian radical
may be supplied as `IsMulCommutative`; no ambient normality is inferred. -/
theorem vertex_two_core_le_its_centralizer
    (V V₂ Y : Subgroup G)
    (hcomm :
      let W := generatedLineFamily V Y
      let P := MulAction.stabilizer (MulAut W)
        (V₂.subgroupOf W)
      IsMulCommutative (P.pCoreIn 2)) :
    let W := generatedLineFamily V Y
    let P := MulAction.stabilizer (MulAut W)
      (V₂.subgroupOf W)
    P.pCoreIn 2 ≤ centralizer (P.pCoreIn 2 : Set (MulAut W)) := by
  dsimp only at hcomm ⊢
  exact le_centralizer_iff_isMulCommutative.mpr hcomm

/-- The irreducibility formula from the actual 14.7.55 action, written in
conjugation form on the literal radical.  The small wrapper below translates
normalizer language into this source action language. -/
def RadicalIrreducibility (W : Subgroup G)
    (P R : Subgroup (MulAut W)) : Prop :=
  ∀ C : Subgroup (MulAut W), C ≤ R →
    (∀ p : P, ∀ r : R, (r : MulAut W) ∈ C →
      (p : MulAut W) * (r : MulAut W) * (p : MulAut W)⁻¹ ∈ C) →
    C = ⊥ ∨ C = R

/-- The source action's conjugation irreducibility yields the normalizer form
needed by `local_image_saturation`. -/
theorem radical_irreducibility_of_source
    (W : Subgroup G) (P R : Subgroup (MulAut W))
    (hsource : RadicalIrreducibility W P R) :
    ∀ C : Subgroup (MulAut W), C ≤ R →
      P ≤ normalizer (C : Set (MulAut W)) → C = ⊥ ∨ C = R := by
  intro C hCR hPC
  apply hsource C hCR
  intro p r hr
  exact (mem_normalizer_iff.mp (hPC p.property) (r : MulAut W)).mp hr

/-- The full span image calculation.  The one-sided cover, residual-image
normality, residual-core seed, radical commutativity, and radical
irreducibility are precisely the source formulas supplied by the preceding
14.7.55/module calculation.  Every equality used to feed saturation is
proved here from those formulas. -/
theorem source_span_full_image
    (V V₂ Y : Subgroup G) (hV₂ : V₂ ≤ V)
    (hspan : normalizer (V₂ : Set G) ≤
      normalizer (generatedLineFamily V Y : Set G))
    (hYV : Y ≤ normalizer (V₂ : Set G))
    (hcover :
      let W := generatedLineFamily V Y
      let ρ := @ambientAction G _ (normalizer (V₂ : Set G)) W hspan
      let P := MulAction.stabilizer (MulAut W)
        (V₂.subgroupOf W)
      P ≤ ρ.range ⊔ P.pCoreIn 2)
    (hPnormal :
      let W := generatedLineFamily V Y
      let ρ := @ambientAction G _ (normalizer (V₂ : Set G)) W hspan
      let P := MulAction.stabilizer (MulAut W)
        (V₂.subgroupOf W)
      P ≤ normalizer (ρ.range : Set (MulAut W)))
    (hnormal :
      let W := generatedLineFamily V Y
      let ρ := @ambientAction G _ (normalizer (V₂ : Set G)) W hspan
      let σ := @ambientAction G _ Y W (hYV.trans hspan)
      ρ.range ≤ normalizer (σ.range : Set (MulAut W)))
    (hseed :
      let W := generatedLineFamily V Y
      let σ := @ambientAction G _ Y W (hYV.trans hspan)
      ∃ D : Subgroup (MulAut W), D ≤ σ.range.pCoreIn 2 ∧ D ≠ ⊥)
    (hcomm :
      let W := generatedLineFamily V Y
      let P := MulAction.stabilizer (MulAut W)
        (V₂.subgroupOf W)
      IsMulCommutative (P.pCoreIn 2))
    (hirr :
      let W := generatedLineFamily V Y
      let P := MulAction.stabilizer (MulAut W)
        (V₂.subgroupOf W)
      RadicalIrreducibility W P (P.pCoreIn 2)) :
    let W := generatedLineFamily V Y
    let ρ := @ambientAction G _ (normalizer (V₂ : Set G)) W hspan
    ρ.range = MulAction.stabilizer (MulAut W) (V₂.subgroupOf W) := by
  dsimp only at hcover hPnormal hnormal hseed hcomm hirr ⊢
  let W := generatedLineFamily V Y
  let N := normalizer (V₂ : Set G)
  let ρ := @ambientAction G _ N W hspan
  let σ := @ambientAction G _ Y W (hYV.trans hspan)
  let P := MulAction.stabilizer (MulAut W) (V₂.subgroupOf W)
  let R := P.pCoreIn 2
  have hρP : ρ.range ≤ P := by
    exact ambient_span_action_range_le_stabilizer V V₂ Y hV₂ hspan
  have hcover' : ρ.range ⊔ R = P := by
    apply le_antisymm
    · exact sup_le hρP (pCoreIn_le 2 P)
    · exact hcover
  have hcore : ρ.range.pCoreIn 2 ≤ R := by
    exact pCoreIn_mono_of_normalizes hρP hPnormal
  have hYcore : σ.range.pCoreIn 2 ≤ ρ.range.pCoreIn 2 := by
    exact local_residual_two_core_le_vertex_two_core V V₂ Y hYV hspan hnormal
  have hYne : σ.range.pCoreIn 2 ≠ ⊥ := by
    intro hzero
    obtain ⟨D, hD, hDne⟩ := hseed
    exact hDne (le_antisymm (hzero ▸ hD) bot_le)
  have habelian : R ≤ centralizer (R : Set (MulAut W)) := by
    exact vertex_two_core_le_its_centralizer V V₂ Y hcomm
  have hirr' : ∀ C : Subgroup (MulAut W), C ≤ R →
      P ≤ normalizer (C : Set (MulAut W)) → C = ⊥ ∨ C = R := by
    exact radical_irreducibility_of_source W P R hirr
  exact local_image_saturation ρ.range σ.range R P hcover' hcore
    hYcore hYne habelian hirr'

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
