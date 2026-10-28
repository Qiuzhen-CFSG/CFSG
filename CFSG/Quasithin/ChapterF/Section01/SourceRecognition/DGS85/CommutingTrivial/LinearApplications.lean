module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AdjacentLinear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.MixedResidual

/-!
# The small-neighbor linear conclusions with source 6.5 discharged

The actual adjacent SL₂ markings supply the complete edge obstruction.
Apply it to the original center and whole residual-section consumers:
the field orders and the three original indices coincide, Z_alpha is natural,
and V_beta/C_V_beta(O²(L_beta)) is natural with its literal conjugation.
The two core commutator identities are also retained. No original-endpoint
marking, residual descent, or adjacent-core obstruction is assumed.

This remains conditional on the two actual linear quotient markings and
the small-neighbor containment. Initial recognition, the reciprocal branch
and the distance/field-two conclusions remain Chapter 9 obligations.
Source: DGS, Groups and Graphs (1985), 6.5, pp.121--122, and 9.3--9.4,
pp.142--143; corrected 5.12 supplies the natural-module step.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The original mixed indices, natural center and 9.4(c), with 6.5 proved from the supplied adjacent markings. -/
theorem reduced_small_neighbor_linear_conclusions (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (hs : V (Reduction.reducedFamily L S₀) a' 1 ≤ Q (Reduction.reducedFamily L S₀) beta)
    {F K : Type*} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [CharP K 2]
    {n m : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hm : 0 < m) (hK : Nat.card K = 2^m)
    (eα : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,F))
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,K)) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    let q := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    Nat.card F = Nat.card K ∧
      (Q Γ a).relIndex (V Γ a' 1) = Nat.card F ∧
      (Q Γ a').relIndex (Z Γ a) = Nat.card F ∧
      (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
      ⁅Q Γ beta,Z Γ a⁆ = Z Γ beta ∧ ⁅V Γ beta 1,Q Γ beta⁆ = Z Γ beta ∧
      ∃ (ρ : Representation (ZMod 2) SL(2,F) (Additive (Z Γ a))) (T : Sylow 2 SL(2,F)),
        (∀ (l : H) (z : Additive (Z Γ a)),
          ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
            (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
        Function.Injective ρ ∧ IsSourceNatural ρ T n ∧
        ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → F),
          ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z) := by
  have hob := adjacent_linear_graph_core_obstruction (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab eα eβ
  exact reduced_small_neighbor_linear_recognition h hc hab hd hb hcomm htriv hs hob hn hF hm hK eα eβ

/-- The whole literal residual section is natural; all descent, generation and 6.5 premises are discharged. -/
theorem reduced_small_neighbor_linear_natural_residual (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (hs : V (Reduction.reducedFamily L S₀) a' 1 ≤ Q (Reduction.reducedFamily L S₀) beta)
    {F K : Type*} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [CharP K 2]
    {n m : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hm : 0 < m) (hK : Nat.card K = 2^m)
    (eα : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,F))
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,K)) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ beta
    let A := (V Γ beta 1).subgroupOf H
    let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    letI : ∀ i, Finite (Γ i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
    ∃ hb2 : 2 < b Γ,
      letI := neighborhoodIn_elementary Γ (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) beta hb2 H
      letI : Algebra (ZMod 2) K := ZMod.algebra K 2
      ∃ (σ : Representation (ZMod 2) SL(2,K) (FixedQuotient A (pResidual 2 H)))
        (T : Sylow 2 SL(2,K)),
        (∀ l : H, σ (q l) = fixedQuotientAction A (pResidual 2 H) l) ∧
        Function.Injective σ ∧ IsSourceNatural σ T m ∧
        ∃ E : FixedQuotient A (pResidual 2 H) ≃ₗ[ZMod 2] (Fin 2 → K),
          ∀ g z, E (σ g z) = Matrix.mulVec g.val (E z) := by
  have hob := adjacent_linear_graph_core_obstruction (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab eα eβ
  exact reduced_small_neighbor_natural_residual h hc hab hd hb hcomm htriv hs hob hn hF hm hK eα eβ

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
