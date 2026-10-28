module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryInvolutions

/-!
# The numerical end of the large-unitary branch

The involution estimates in `UnitaryInvolutions` give a square lower bound on
the original displacement index.  Chapter 8 obtains the matching linear upper
bound from the neighboring quotient action.  These two small assembly lemmas
record the resulting contradiction while retaining the original center,
moving neighbor and quotient equivalence.

Source: DGS, *Groups and Graphs* (1985), (8.2)(**)--(8.3), pp.134--137.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G]

/-- A special-unitary actor cannot satisfy the linear upper index bound once
the literal source involution estimate is available. -/
theorem source_special_unitary_index_upper_contradiction
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)}
    (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P))
    (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P),
      IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃*
      J.specialSubgroup)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAE : A ≤ (stabilizer (family P) w.val ⊓
      stabilizer (family P) a').pCoreIn 2)
    (hAQ : ¬ A ≤ Q (family P) w.val)
    (hupper : (centralizer (A : Set G)).relIndex
      (Z (family P) w.val) ≤ 2^n) : False := by
  have hl := source_moving_special_unitary_involution_field_square_bound h hB d
    hc hab hd hb hcomm models w hm J hn hK hconj e A hAE hAQ
  have hq : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
  have hle : (2^n)^2 ≤ 2^n := hl.trans hupper
  nlinarith only [hq, hle]

/-- The same contradiction for the projective-unitary quotient.  The odd
scalar kernel is retained by the actual projective involution estimate. -/
theorem source_projective_unitary_index_upper_contradiction
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)}
    (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P))
    (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P),
      IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAE : A ≤ (stabilizer (family P) w.val ⊓
      stabilizer (family P) a').pCoreIn 2)
    (hAQ : ¬ A ≤ Q (family P) w.val)
    (hupper : (centralizer (A : Set G)).relIndex
      (Z (family P) w.val) ≤ 2^n) : False := by
  have hl := source_moving_projective_unitary_involution_field_square_bound h hB d
    hc hab hd hb hcomm models w hm J hn hK hconj e A hAE hAQ
  have hq : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
  have hle : (2^n)^2 ≤ 2^n := hl.trans hupper
  nlinarith only [hq, hle]

/-- Literal reduced-F1.11 transport of the special-unitary contradiction. -/
theorem reduced_special_unitary_index_upper_contradiction
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
    (hd : (graph (Reduction.reducedFamily J S)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S))
    (hb : 1 < b (Reduction.reducedFamily J S))
    (hcomm : ⁅Z (Reduction.reducedFamily J S) a,
      Z (Reduction.reducedFamily J S) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S) beta 1 ⊓
      Q (Reduction.reducedFamily J S) a',
      Z (Reduction.reducedFamily J S) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K]
    (M : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, M.conj x = x^(2^n))
    (e : (graphLocalGroup (Reduction.reducedFamily J S) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) w.val)) ≃*
      M.specialSubgroup)
    (A : Subgroup (Reduction.G₀ J S)) [IsElementaryAbelian 2 A]
    (hAE : A ≤ (stabilizer (Reduction.reducedFamily J S) w.val ⊓
      stabilizer (Reduction.reducedFamily J S) a').pCoreIn 2)
    (hAQ : ¬ A ≤ Q (Reduction.reducedFamily J S) w.val)
    (hupper : (centralizer (A : Set (Reduction.G₀ J S))).relIndex
      (Z (Reduction.reducedFamily J S) w.val) ≤ 2^n) : False := by
  exact source_special_unitary_index_upper_contradiction
    (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h)
    (Reduction.reducedEarlierLocalTheorems h hob) hc hab hd hb hcomm models w hm M hn hK
    hconj e A hAE hAQ hupper

/-- Literal reduced-F1.11 transport of the projective-unitary contradiction. -/
theorem reduced_projective_unitary_index_upper_contradiction
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
    (hd : (graph (Reduction.reducedFamily J S)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S))
    (hb : 1 < b (Reduction.reducedFamily J S))
    (hcomm : ⁅Z (Reduction.reducedFamily J S) a,
      Z (Reduction.reducedFamily J S) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S) beta 1 ⊓
      Q (Reduction.reducedFamily J S) a',
      Z (Reduction.reducedFamily J S) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K]
    (M : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, M.conj x = x^(2^n))
    (e : (graphLocalGroup (Reduction.reducedFamily J S) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) w.val)) ≃*
      ProjectiveSpecialUnitaryMatrixGroup M)
    (A : Subgroup (Reduction.G₀ J S)) [IsElementaryAbelian 2 A]
    (hAE : A ≤ (stabilizer (Reduction.reducedFamily J S) w.val ⊓
      stabilizer (Reduction.reducedFamily J S) a').pCoreIn 2)
    (hAQ : ¬ A ≤ Q (Reduction.reducedFamily J S) w.val)
    (hupper : (centralizer (A : Set (Reduction.G₀ J S))).relIndex
      (Z (Reduction.reducedFamily J S) w.val) ≤ 2^n) : False := by
  exact source_projective_unitary_index_upper_contradiction
    (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h)
    (Reduction.reducedEarlierLocalTheorems h hob) hc hab hd hb hcomm models w hm M hn hK
    hconj e A hAE hAQ hupper

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
