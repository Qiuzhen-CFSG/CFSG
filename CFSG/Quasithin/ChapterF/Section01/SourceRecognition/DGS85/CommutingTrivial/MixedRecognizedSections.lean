module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.MixedInitialRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.LinearApplications

/-!
# The actual small-neighbor conclusions of DGS 9.3--9.4

The mixed-module comparison constructs both adjacent linear markings from
the full earlier quotient catalogues. Feed those markings into the existing
natural-center and whole-residual-section constructions. Both original
field parameters, all three core indices, the two 9.4(c) commutators and
the exact conjugation/descent equations are retained. The residual action
is constructed on the whole V_beta/C_V_beta(O²(L_beta)).

The catalogue and earlier source 6.5 inputs remain to be discharged by their
source producers. This proves the small-neighbor branch at that boundary;
the general reciprocal branch and 9.5--9.11 remain with Chapter 9 assembly.
Source: DGS, Groups and Graphs (1985), 9.3--9.4, printed pp.142--143.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Original small-neighbor 9.3--9.4 with both markings, both natural modules,
all original indices and the literal maps constructed from the source catalogues. -/
theorem reduced_small_neighbor_recognized_sections (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (hs : V (Reduction.reducedFamily L S₀) a' 1 ≤ Q (Reduction.reducedFamily L S₀) beta)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a'))) :
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (n m : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧ 0 < m ∧ Nat.card K = 2^m ∧
      ∃ eα : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,F),
      ∃ eβ : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,K),
      (let Γ := Reduction.reducedFamily L S₀
       V Γ beta 1 = Z Γ a ⊔ (V Γ beta 1 ⊓ Q Γ a') ∧
         (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) = Nat.card K ∧
         (centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) = Nat.card K) ∧
      (let Γ := Reduction.reducedFamily L S₀
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
             ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) ∧
      (let Γ := Reduction.reducedFamily L S₀
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
             ∀ g z, E (σ g z) = Matrix.mulVec g.val (E z)) := by
  obtain ⟨_,F,instF,finF,charF,K,instK,finK,charK,n,m,hn,hF,hm,hK,⟨eα⟩,⟨eβ⟩⟩ :=
    reduced_small_neighbor_linear_markings h hc hab hd hb hcomm htriv hs hob Mα Mα'
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  have hcenter := reduced_small_neighbor_linear_conclusions h hc hab hd hb hcomm htriv hs
    hn hF hm hK eα eβ
  obtain ⟨hspan,_,hreverse⟩ := reduced_small_neighbor_span_and_centralizer h hc hab hd hb
    hcomm htriv hs hob hn hF hm hK eα eβ
  have hforward := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ beta 1))
    (reduced_neighbor_centralizer_eq_core_inter h beta a' hb hd htriv)
  change (V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) =
    (V Γ beta 1 ⊓ Q Γ a').relIndex (V Γ beta 1) at hforward
  simp only [inf_relIndex_left] at hforward
  exact ⟨F,instF,finF,charF,K,instK,finK,charK,n,m,hn,hF,hm,hK,eα,eβ,
    ⟨hspan,hforward.trans (hcenter.2.2.2.1.trans hcenter.1),hreverse⟩,hcenter,
    reduced_small_neighbor_linear_natural_residual h hc hab hd hb hcomm htriv hs hn hF hm hK eα eβ⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
