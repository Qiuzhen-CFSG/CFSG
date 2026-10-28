module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.SourceGeometry
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Assembly
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics

/-!
# Assembly of the marked module geometry

The natural and Weyl calculations give all eight clauses of 14.7.55 on
one literal quotient. The incidence hexagon and the collinearity graph
are retained separately. The subsequent source applications use these
marked calculations to supply the local-action and parabolic consumers.

The equivariant module identification and earlier local identities remain
with the 14.7.53 assembly owner. Only the precise earlier B.4.6 offender
premises remain model inputs, owned by qt-b-04-g2.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1066–1067, Lemmas 14.7.55–57.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Assembly
open Atlas.G2 Atlas.G2.Natural Atlas.SplitOctonion
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Subgroup Representation Representation.BinaryOffender
open MarkedPencil MarkedPencil.Assembly MarkedPencil.SourceActions.ResidualAction
open LocalParabolics LocalParabolics.ThreeOffenderOrbit

/-- Metric assertions for the actual incidence geometry, with a separate
assertion for the graph on singular points. This is an output record. -/
structure HexagonConclusions {Q : Type*} [Group Q] (geom : QuotientGeometry Q) : Prop where
  girth : ∀ P (w : (realizedIncidence geom).Walk P P), w.IsCycle → 12 ≤ w.length
  diameter : ∀ x y, ∃ w : (realizedIncidence geom).Walk x y, w.length ≤ 6
  no_four_cycle : ∀ P (w : (realizedCollinearity geom).Walk P P),
    w.IsCycle → w.length ≠ 4

private theorem hexagon_conclusions {Q : Type*} [Group Q] (geom : QuotientGeometry Q) :
    HexagonConclusions geom :=
  ⟨realizedIncidence_girth geom, realizedIncidence_diameter geom,
    realizedCollinearity_no_four_cycle geom⟩

variable {H D : Type*} [Group H] [Finite H] [Group D]

/-- All eight clauses of 14.7.55, on the same natural or Weyl source
quotient. The point and line are constructed from the local marking data;
neither the geometry nor a target clause is a hypothesis. -/
theorem source_marked_geometry
    (m : BinaryG2Module)
    (U V₁ V₂ V L₁ : Subgroup H) [U.Normal] [(V₁.subgroupOf U).Normal]
    [IsElementaryAbelian 2 V₁] [MulDistribMulAction D (U ⧸ V₁.subgroupOf U)]
    (h12 : V₁ ≤ V₂) (h2V : V₂ ≤ V) (hVU : V ≤ U)
    (hlocal : ⁅V,L₁⁆ ⊔ V₁ = V)
    (hcentral : (⊤ : Subgroup H) ≤ centralizer (V₁ : Set H))
    (π : H →* D) (hπ : Function.Surjective π)
    (i : D →* Model (ZMod 2)) (hi : Function.Injective i)
    (hJ : commutator (Model (ZMod 2)) ≤ i.range) (hk : IsPGroup 2 (i.comp π).ker)
    (e : Multiplicative (m.Space) ≃* U ⧸ V₁.subgroupOf U)
    (he : ∀ d w, d • e (Multiplicative.ofAdd w) =
      e (Multiplicative.ofAdd (m.action (i d) w)))
    (hact : ∀ (h : H) (u : U), m.action (i (π h))
        (e.symm (QuotientGroup.mk' (V₁.subgroupOf U) u)).toAdd =
      (e.symm (QuotientGroup.mk' (V₁.subgroupOf U)
        ⟨h * (u : H) * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩)).toAdd)
    (hcardV : Nat.card ((V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 4)
    (hcardV₂ : Nat.card ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 2)
    (T : Sylow 2 H) (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hT₂ : (T : Subgroup H) ≤ normalizer (V₂ : Set H))
    (hRank : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A ≤ 2)
    (hOne : ∀ A : Subgroup (Model (ZMod 2)), IsElementaryTwo A →
      rank A = 1 → 2 ≤ fixedCodim m.action A)
    (hTwo : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A = 2 → 3 ≤ fixedCodim m.action A)
    (hB46 : ∀ B : Subgroup (Model (ZMod 2)), IsBestOffender m.action B ↔
      ∃ g : Model (ZMod 2), BinaryCore.elementary.map (MulAut.conj g).toMonoidHom = B) :
    ∃ p : SingularPoints (ZMod 2),
      SourceConclusions U V₁ V₂ V m.action m.singularMap e π i T p ∧
      HexagonConclusions (transportGeometry m.singularMap.geometry e) := by
  have hs : ∃ p, SourceConclusions U V₁ V₂ V m.action m.singularMap e π i T p := by
    cases m with
    | natural =>
      exact natural_source_conclusions U V₁ V₂ V h12 h2V hVU hcentral π hπ i hi hJ hk
        e he hact hcardV hcardV₂ T hTV hT₂ hRank hOne hTwo hB46
    | weyl =>
      exact weyl_source_conclusions U V₁ V₂ V L₁ h12 h2V hVU hlocal hcentral π hπ i hi hJ hk
        e he hact hcardV hcardV₂ T hTV hT₂ hRank hOne hTwo hB46
  obtain ⟨p,hp⟩ := hs
  exact ⟨p,hp,hexagon_conclusions _⟩

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Assembly
