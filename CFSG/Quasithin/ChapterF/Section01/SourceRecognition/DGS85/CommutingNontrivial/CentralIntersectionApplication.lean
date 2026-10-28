module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralIntersectionRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ResidualSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction

/-!
# The opposite index bound on the original residual section

The reduced F1.11 geometry constructs the nonzero section
`V_beta / C_(V_beta)(O²(L_beta))`, its original conjugation action, zero
residual fixed space, and the quadratic opposite actor. The opposite
centralizer estimate bounds its fixed-space quotient for each moving
neighbor by the product of the two literal quotient-Sylow omega orders.

This is the upper comparison used in DGS, *Groups and Graphs* (1985),
8.6, printed pp.139--140. The lower comparison and natural-module exclusion
remain separate mathematical obligations.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The actual residual-section upper bound, with its denominator, action,
and both quotient-Sylow parameters constructed on the reduced source graph. -/
theorem reduced_opposite_residual_index_le_omega_product
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,
      Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (T : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) :
    let F := Reduction.reducedFamily J S₀
    let L := graphLocalGroup F beta
    let A := (V F beta 1).subgroupOf L
    letI : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal F beta L (sylowGenerated_le _)
    ∃ hb2 : 2 < b F,
      letI := neighborhoodIn_elementary F (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) beta hb2 L
      let ρ := fixedQuotientAction A (pResidual 2 L)
      Nontrivial (FixedQuotient A (pResidual 2 L)) ∧
      Nonempty (BinaryConjugationSection L (V F beta 1)
        (V F beta 1 ⊓ centralizer ((pResidual 2 L).map L.subtype : Set (Reduction.G₀ J S₀))) ρ) ∧
      fixedSpace ρ (pResidual 2 L) = ⊥ ∧
      IsQuadratic ρ ((V F a' 1).subgroupOf L) ∧
      Nat.card (FixedQuotient A (pResidual 2 L) ⧸ fixedSpace ρ ((Z F w.val).subgroupOf L)) ≤
        Nat.card (omegaCenterIn ((T : Subgroup (graphLocalGroup F a')).map
          (QuotientGroup.mk' (pCore 2 (graphLocalGroup F a'))))) *
        Nat.card (omegaCenterIn ((R : Subgroup (graphLocalGroup F w.val)).map
          (QuotientGroup.mk' (pCore 2 (graphLocalGroup F w.val))))) := by
  let F := Reduction.reducedFamily J S₀
  let L := graphLocalGroup F beta
  let A := (V F beta 1).subgroupOf L
  let : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple h)
  let : A.Normal := neighborhoodIn_normal F beta L (sylowGenerated_le _)
  obtain ⟨hb2,hn,⟨c⟩,hr,_,hq⟩ :=
    CommutingTrivial.reduced_critical_residual_section h hc hab hd hb hcomm
  let : IsElementaryAbelian 2 A := neighborhoodIn_elementary F (Reduction.reduced_triple h).generate
    (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 L
  refine ⟨hb2,hn,⟨c⟩,hr,hq,?_⟩
  have hi := source_opposite_section_index_le_omega_product (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedFullEarlierLocalTheorems h)
    models hc hab hd hb hcomm w hm R T (fixedQuotientAction A (pResidual 2 L))
    (MonoidHom.id L) _ c
  change Nat.card (FixedQuotient A (pResidual 2 L) ⧸
    fixedSpace (fixedQuotientAction A (pResidual 2 L))
      (((Z F w.val).subgroupOf L).map (MonoidHom.id L))) ≤ _ at hi
  rw [Subgroup.map_id] at hi
  exact hi

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
