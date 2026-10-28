module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.InitialAlphaBounds

/-!
# Strict alpha selection from the constructed omega action

The preceding 9.4 development constructs the actual alpha Sylow, its
quotient omega-center and the sharp fixed-index bound.  This extension keeps
the source's literal Sylow-to-completion map and exposes the remaining
strict-square implication as a direct consumer.  The strictness premise is
the normalized opposite-omega comparison still supplied by the Chapter 9
assembly; no quotient tag is treated as an alpha recognition theorem.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The strict normalized-omega comparison feeds the actual alpha quotient
selection in 9.4.  The premise is stated for every Sylow representative with
the source's full-edge image, so the chosen representative from the omega
bound is covered literally.
-/
theorem reduced_critical_alpha_model_of_normalized_strict
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (Mbin : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (M : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hres : NaturalResidualSection h beta e n)
    (hstrict : ∀ (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)),
      (R : Subgroup (graphLocalGroup (Reduction.reducedFamily L S₀) a)).map
          (graphLocalGroup (Reduction.reducedFamily L S₀) a).subtype =
        (stabilizer (Reduction.reducedFamily L S₀) a ⊓
          stabilizer (Reduction.reducedFamily L S₀) beta).pCoreIn 2 →
      Nat.card F < Nat.card (omegaCenterIn
        ((R : Subgroup (graphLocalGroup (Reduction.reducedFamily L S₀) a)).map
          (QuotientGroup.mk' (pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a))))) ^ 2) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ),
      0 < m ∧ Nat.card K = 2^m ∧
        Nonempty ((H ⧸ pCore 2 H) ≃* SL(2,K)) := by
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a
  obtain ⟨R,hR,_,_,_,_,hbound,hselect⟩ :=
    reduced_natural_residual_omega_bound h hob hc hab hd hb hcomm Mbin M hn hF e hres
  dsimp only
  exact hselect.2 (hstrict R hR)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
