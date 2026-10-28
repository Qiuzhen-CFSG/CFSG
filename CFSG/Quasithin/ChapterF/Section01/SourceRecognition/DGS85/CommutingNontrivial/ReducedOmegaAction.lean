module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaModule
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReducedNormality

/-!
# Original 8.1(h) in the reduced F1.11 configuration

The original nontrivial H supplies the moving neighbor. The reduced source
triple constructs an actual full-edge Sylow T and a local Sylow R with the
same ambient image. The full quotient omega-center then centralizes H and
acts quadratically on Z_lambda, both as a subgroup identity and as the
actual binary representation with its conjugation formula.

All vertices are arbitrary, so the statement permits the opposite critical
pair needed by 9.2. The only extra earlier inputs are source 6.1 quotient
models and the 6.5 obstruction, supplied by the shared source assembly.
This proves the 8.1(h) step, not the reciprocal escape or final conclusions
of 8.2–8.7. Source: DGS, *Groups and Graphs* (1985), pp.132–134.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- Original 8.1(h) on the reduced F1.11 graph. The full-edge Sylow and
moving neighbor are constructed from the original nontrivial commutator.
Every ordered critical pair is allowed, as required for reorientation in 9.2. -/
theorem reduced_critical_quotient_omega_action
    {J : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 J S)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S),
      (graph (Reduction.reducedFamily J S)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S) w ⊓ Q (Reduction.reducedFamily J S) v :
          Subgroup (Reduction.G₀ J S)) : Set (Reduction.G₀ J S)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S) a a')
    (hab : (graph (Reduction.reducedFamily J S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S)).dist beta a' + 1 = b (Reduction.reducedFamily J S))
    (hb : 1 < b (Reduction.reducedFamily J S))
    (hcomm : ⁅Z (Reduction.reducedFamily J S) a, Z (Reduction.reducedFamily J S) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S) beta 1 ⊓ Q (Reduction.reducedFamily J S) a',
      V (Reduction.reducedFamily J S) a' 1⁆ ≠ ⊥) :
    let F := Reduction.reducedFamily J S
    let H := ⁅V F beta 1 ⊓ Q F a', V F a' 1⁆
    ∃ (w : (graph F).neighborSet a')
      (T : Sylow 2 ↥(stabilizer F w.val ⊓ stabilizer F a' : Subgroup (Reduction.G₀ J S)))
      (R : Sylow 2 (graphLocalGroup F w.val)),
      (T : Subgroup ↥(stabilizer F w.val ⊓ stabilizer F a' : Subgroup (Reduction.G₀ J S))).map
        (stabilizer F w.val ⊓ stabilizer F a').subtype =
          (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype ∧
      ⁅V F beta 1 ⊓ Q F a', Z F w.val⁆ ≠ ⊥ ∧
      (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype =
        (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 ∧
      (let Y := quotientSylowOmegaPreimage (graphLocalGroup F w.val) R
       H ≤ Z F w.val ⊓ centralizer (Y : Set (Reduction.G₀ J S)) ∧
         ⁅⁅Z F w.val,Y⁆,Y⁆ = ⊥) ∧
      (letI : IsElementaryAbelian 2 (Z F w.val) :=
         CommutingOneProfile.source_center_elementary (Reduction.reduced_triple h) w.val
       let L := graphLocalGroup F w.val
       let q := QuotientGroup.mk' (pCore 2 L)
       ∃ ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive (Z F w.val)),
         (∀ (l : L) (z : Additive (Z F w.val)),
           ((ρ (q l) z).toMul : Reduction.G₀ J S) =
             (l : Reduction.G₀ J S) * z.toMul * (l : Reduction.G₀ J S)⁻¹) ∧
         IsQuadratic ρ (omegaCenterIn ((R : Subgroup L).map q))) := by
  let h' := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let hB := Reduction.reduced_borel_core_sylow h
  let F := Reduction.reducedFamily J S
  dsimp only
  obtain ⟨w, hw, _⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U h' v).1) beta a' hne
  obtain ⟨R, hR⟩ := source_edge_core_local_sylow h' hB d w.property.symm
  obtain ⟨T, hT⟩ := source_edge_core_sylow h' hB w.property.symm
  exact ⟨w, T, R, (by rw [hT]; exact hR.symm), hw, hR,
    source_critical_quotient_omega_action h' hB d hc hab hd hb hcomm models w hw R hR,
    source_critical_quotient_omega_module h' hB d hc hab hd hb hcomm models w hw R hR⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
