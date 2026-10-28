module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.GraphRadius
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.NaturalEndpoints

/-!
# Natural critical sections feed the graph radius escapes

For the literal source graph, elementary abelianness and core centralization
are discharged from the original triple. The natural-section counting proves
field-parameter equality and the opposite-center Sylow product. The odd
relative index of the local actor then lifts that product to the full vertex
stabilizer, where it supplies the (7.2) radius argument.

This is an actual conditional application, not the whole Chapter 7 theorem.
The SL₂ identifications and equivariant natural coordinates remain inputs,
as do the earlier local Sylow facts, actor placement/index, and maximality
of the local point stabilizers. The generating neighbor is constructed. The radius-one implication retains exactly the (6.6) obstruction.
These premises and the (7.3)--(7.5) distance argument remain for source assembly.

Source: DGS, *Groups and Graphs* (1985), (6.0), (7.1)--(7.2), pp.118,126--127.
-/

public section
open Subgroup Representation Representation.BinaryConjugationSection
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G]

/-- Apply the marked center-section proof through the actual quotient maps
and full vertex stabilizers; no Sylow product or parameter equality is assumed. -/
theorem graph_radius_escapes_of_natural_sections
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hb : 2 < b (family P))
    (L₀ L₁ : Subgroup G)
    [(((stabilizer (family P) v).pCoreIn 2).subgroupOf L₀).Normal]
    [(((stabilizer (family P) w).pCoreIn 2).subgroupOf L₁).Normal]
    {W₀ W₁ F₀ F₁ : Type*}
    [AddCommGroup W₀] [Module (ZMod 2) W₀]
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
    [Field F₀] [Finite F₀] [CharP F₀ 2] [Algebra (ZMod 2) F₀]
    [Field F₁] [Finite F₁] [CharP F₁ 2] [Algebra (ZMod 2) F₁]
    (σ₀ : Representation (ZMod 2) (L₀ ⧸ ((stabilizer (family P) v).pCoreIn 2).subgroupOf L₀) W₀)
    (σ₁ : Representation (ZMod 2) (L₁ ⧸ ((stabilizer (family P) w).pCoreIn 2).subgroupOf L₁) W₁)
    (d₀ : BinaryConjugationSection L₀ (Z (family P) v) (Stellmacher.omegaOneCenterAmbient L₀)
      (σ₀.comp (QuotientGroup.mk' (((stabilizer (family P) v).pCoreIn 2).subgroupOf L₀))))
    (d₁ : BinaryConjugationSection L₁ (Z (family P) w) (Stellmacher.omegaOneCenterAmbient L₁)
      (σ₁.comp (QuotientGroup.mk' (((stabilizer (family P) w).pCoreIn 2).subgroupOf L₁))))
    (e₀ : (L₀ ⧸ ((stabilizer (family P) v).pCoreIn 2).subgroupOf L₀) ≃* SL(2,F₀))
    (e₁ : (L₁ ⧸ ((stabilizer (family P) w).pCoreIn 2).subgroupOf L₁) ≃* SL(2,F₁))
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → F₀))
    (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → F₁))
    (he₀ : ∀ g w, E₀ (σ₀ g w) = Matrix.mulVec (e₀ g).val (E₀ w))
    (he₁ : ∀ g w, E₁ (σ₁ g w) = Matrix.mulVec (e₁ g).val (E₁ w))
    (hL₀ : L₀ ≤ (stabilizer (family P) v)) (hL₁ : L₁ ≤ (stabilizer (family P) w))
    (h₁₀ : (Z (family P) w) ≤ L₀) (h₀₁ : (Z (family P) v) ≤ L₁)
    (hQ₀ : (stabilizer (family P) v).pCoreIn 2 ≤ L₀) (hQ₁ : (stabilizer (family P) w).pCoreIn 2 ≤ L₁)
    (hS₀ : Stellmacher.IsSylowSubgroupIn ((stabilizer (family P) v).pCoreIn 2) (L₀ ⊓ centralizer ((Z (family P) v) : Set G)))
    (hS₁ : Stellmacher.IsSylowSubgroupIn ((stabilizer (family P) w).pCoreIn 2) (L₁ ⊓ centralizer ((Z (family P) w) : Set G)))
    (hne : ⁅(Z (family P) v),(Z (family P) w)⁆ ≠ ⊥)
    (hindex : ¬ 2 ∣ L₁.relIndex (stabilizer (family P) w))
    (hmax : ∀ u, (graph (family P)).Adj v u →
      IsCoatom ((stabilizer (family P) u).subgroupOf (stabilizer (family P) v))) :
    Nat.card F₀ = Nat.card F₁ ∧
      (¬ V (family P) v 2 ≤ stabilizer (family P) w) ∧
      ((∀ u, (graph (family P)).Adj v u → ¬ stabilizer (family P) v ≤
          normalizer ((Z (family P) u ⊔ Z (family P) v : Subgroup G) : Set G)) →
        ¬ V (family P) v 1 ≤ stabilizer (family P) w) := by
  let := finite_endpoints h
  let := graph_Z_elementary h v
  let := graph_Z_elementary h w
  have hn := source_natural_endpoints (stabilizer (family P) v) (stabilizer (family P) w)
    L₀ L₁ (Z (family P) v) (Z (family P) w) σ₀ σ₁ d₀ d₁ e₀ e₁ E₀ E₁
    he₀ he₁ hL₀ hL₁ h₁₀ h₀₁ hQ₀ hQ₁
    (graph_Q_centralizes_Z h v) (graph_Q_centralizes_Z h w) hS₀ hS₁ hne
  have hs := sylow_in_overgroup_of_odd_relIndex (stabilizer (family P) w) L₁
    (Z (family P) v ⊔ Q (family P) w) hL₁ hn.2.2.1 hindex
  exact ⟨hn.1, graph_radius_two_escape_of_maximal_edges h hS hc hne hb hs hmax,
    graph_radius_one_escape_of_maximal_edges h hS hc hne hb hs hmax⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
