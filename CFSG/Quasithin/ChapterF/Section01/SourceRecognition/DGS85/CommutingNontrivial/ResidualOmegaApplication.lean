module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualDescent
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualComparisonApplication

/-!
# The original reduced residual quotient in the 8.3 counterexample

The original 6.5(a) obstruction supplies adjacent-core escape. The marked
residual intersection equals the quotient omega preimage, and E Q_lambda
is literally E T₀. On the whole V_alpha'/C_V_alpha'(E), the constructed
core-quotient action agrees with the original action on representatives.
The section keeps the original numerator, denominator and coordinate map.

This is the actual reduced F1.11 consumer of the quotient identity and
core-displacement proofs. It retains arbitrary critical orientation and
the full edge Sylow. Naturality exclusion, paired square inequalities,
and the subsequent Chapter 8 conclusions remain with this source family.

Source: DGS, Groups and Graphs (1985), proof of 8.3, pp.135–136.
-/

@[expose] public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G]

open Representation.NormalElementaryQuotient
open CommutingTrivial
variable {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The literal reduced F1.11 residual quotient, with the printed residual
join, exact quotient omega identity and descended original action. -/
theorem reduced_counterexample_residual_quotient_action
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily J S₀) w.val).subtype =
        (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓ stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hbad : ¬ ⁅quotientSylowOmegaPreimage (graphLocalGroup (Reduction.reducedFamily J S₀) w.val) R,
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≤
        ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
          V (Reduction.reducedFamily J S₀) a' 1⁆) :
    let F := Reduction.reducedFamily J S₀
    let L := graphLocalGroup F a'
    let U := (V F a' 1).subgroupOf L
    let T := (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype
    let E := (pResidual 2 L).map L.subtype
    let D := E ⊔ Q F w.val
    let T₀ := T ⊓ D
    letI : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal F a' L (sylowGenerated_le _)
    ∃ hb2 : 2 < b F,
      letI := neighborhoodIn_elementary F (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) a' hb2 L
      T₀ = quotientSylowOmegaPreimage (graphLocalGroup F w.val) R ∧ D = E ⊔ T₀ ∧
      ∃ (hDL : D ≤ L)
        (σ : Representation (ZMod 2) (D ⧸ pCore 2 D) (FixedQuotient U (pResidual 2 L))),
        (∀ g : D, σ (QuotientGroup.mk' (pCore 2 D) g) =
          fixedQuotientAction U (pResidual 2 L) (inclusion hDL g)) ∧
        Nonempty (BinaryConjugationSection D (V F a' 1)
          (V F a' 1 ⊓ centralizer (E : Set (Reduction.G₀ J S₀)))
          (σ.comp (QuotientGroup.mk' (pCore 2 D)))) := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let L := graphLocalGroup F a'
  let U := (V F a' 1).subgroupOf L
  let T := (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype
  let E := (pResidual 2 L).map L.subtype
  let D := E ⊔ Q F w.val
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : U.Normal := neighborhoodIn_normal F a' L (sylowGenerated_le _)
  obtain ⟨hb2,_,⟨c⟩,_,_,_,_⟩ := reduced_ending_residual_actor h hob models hc hab hd hb hcomm w
  refine ⟨hb2,?_⟩
  let : IsElementaryAbelian 2 U := neighborhoodIn_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) a' hb2 L
  have hescape := core_escape_of_intersection_obstruction F (hob w.val a' w.property.symm)
  have he := source_counterexample_residual_edge_eq_omega ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hm hescape R hR hbad
  have hQT : Q F w.val ≤ T := by
    dsimp only [T]
    rw [hR]
    exact Noncommuting.graph_Q_le_edgeCore ht w.property.symm
  have hjoin : D = E ⊔ (T ⊓ D) := le_antisymm
    (sup_le le_sup_left ((le_inf hQT le_sup_right).trans le_sup_right))
    (sup_le le_sup_left inf_le_right)
  obtain ⟨hDL,σ,hσ,cD,_⟩ := source_counterexample_residual_quotient_action ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models w hm hescape R hR hbad
    (fixedQuotientAction U (pResidual 2 L)) c
  exact ⟨he,hjoin,hDL,σ,hσ,⟨cD⟩⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
