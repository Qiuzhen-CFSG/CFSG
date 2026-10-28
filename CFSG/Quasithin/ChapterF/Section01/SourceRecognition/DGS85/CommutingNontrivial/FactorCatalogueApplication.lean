module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FactorCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FactorComparison

/-!
# Applying the ending-factor catalogue to a linear start

The factor dispatcher is now consumed by the actual reciprocal argument.  If
the starting quotient is linear, either the ending-factor index bound or its
square bound feeds the already proved corrected-5.12 escape theorem.  The
only branch left by this literal application is a field-two SU₃/PSU₃ ending
quotient.  The statement keeps the original graph, quotient maps and source
model hypotheses explicit.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Under reverse containment, a linear starting quotient leaves only the
field-two unitary ending rows after the complete literal factor split. -/
theorem reduced_linear_start_factor_catalogue
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
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,
      Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓
      Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2 ^ n)
    (eK : (graphLocalGroup (Reduction.reducedFamily J S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)) ≃* SL(2, K))
    {D : Type u} [Group D] [Finite D]
    (eD : (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* D)
    (hm : IsRankOneModel D) :
    ¬ V (Reduction.reducedFamily J S₀) a' 1 ≤
        Q (Reduction.reducedFamily J S₀) beta ∨
      (ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2) := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let hB := Reduction.reduced_borel_core_sylow h
  let F := Reduction.reducedFamily J S₀
  rcases reduced_ending_factor_bound_or_small_unitary h hc hab hd hb hcomm eD hm with
    hfactor | hfactor | hsmall
  · left
    intro hreverse
    exact source_reciprocal_linear_escape_of_factor_bound ht hB d hc hab hd hb hcomm
      models hne hn hK eK hfactor hreverse
  · left
    intro hreverse
    have hlin : (Q F a').relIndex (Z F a) ≤
        (centralizer (Z F a : Set (Reduction.G₀ J S₀))).relIndex (V F a' 1) :=
      (Nat.le_self_pow (by decide : 2 ≠ 0) _).trans hfactor
    exact source_reciprocal_linear_escape_of_factor_bound ht hB d hc hab hd hb hcomm
      models hne hn hK eK hlin hreverse
  · exact Or.inr hsmall

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
