module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryEndingCommutator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.SuzukiEndingCommutator

/-!
# The remaining ending alternative in DGS 8.3

The literal source quotient catalogue now reduces 8.3 to a linear ending of
field order at least four. Every Suzuki, special-unitary, projective-unitary
and dihedral ending gives the original quotient-omega commutator conclusion,
with its moving neighbor and full-edge Sylow constructed. SL₂(2) is included.
This is a proved reduction, not the unresolved large-field linear conclusion.

Source: DGS85, Groups and Graphs, (8.3), pp.135–137; the actual F1.1 quotient
catalogue, including the odd scalar kernel of SU₃, is retained.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The actual nontrivial commuting source configuration satisfies 8.3 in
every ending row except a possible large-field linear quotient. -/
theorem reduced_omega_commutator_or_large_linear_ending
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',V (Reduction.reducedFamily L S₀) a' 1⁆ ≠ ⊥) :
    let F := Reduction.reducedFamily L S₀
    (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSL (graphLocalGroup F a' ⧸
      pCore 2 (graphLocalGroup F a')) 2 (2^n)) ∨
    (¬ V F a' 1 ≤ Q F beta ∧
      ∃ w : (graph F).neighborSet a',
        ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥ ∧
        ∃ R : Sylow 2 (graphLocalGroup F w.val),
          (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype =
            (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 ∧
          ⁅quotientSylowOmegaPreimage (graphLocalGroup F w.val) R,Z F w.val⁆ ≤
            ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆) := by
  let F := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple h)
  let : Finite (graphLocalGroup F a') :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  cases models a' with
  | linear n hn hi =>
      by_cases hn2 : 2 ≤ n
      · exact Or.inl ⟨n,hn2,hi⟩
      · have hn1 : n = 1 := by omega
        right
        exact reduced_ending_binary_models_omega_commutator h hob models hc hab hd hb hcomm hne
          (Or.inl (by simpa only [hn1,pow_one] using hi))
  | suzuki k hi =>
      right
      exact reduced_ending_suzuki_omega_commutator h hob models hc hab hd hb hcomm hne k hi.some
  | projective_unitary n hn hi =>
      right
      exact reduced_ending_unitary_omega_commutator h hob models hc hab hd hb hcomm hne n hn (Or.inl hi)
  | special_unitary n hn hi =>
      right
      exact reduced_ending_unitary_omega_commutator h hob models hc hab hd hb hcomm hne n hn (Or.inr hi)
  | dihedral hi =>
      right
      apply reduced_ending_two_rank_one_omega_commutator h hob models hc hab hd hb hcomm hne
      rw [primeRank_congr 2 hi.some]
      let S : Sylow 2 (DihedralGroup 5) := Sylow.ofCard (zpowers (DihedralGroup.sr 0 : DihedralGroup 5)) (by
        rw [Nat.card_zpowers,DihedralGroup.orderOf_sr,DihedralGroup.nat_card]
        rw [Nat.factorization_mul (by decide) (by decide),
          Nat.prime_two.factorization,Nat.prime_five.factorization]
        norm_num)
      exact S.primeRank_le_one_of_isCyclic
        (inferInstanceAs (IsCyclic (zpowers (DihedralGroup.sr 0 : DihedralGroup 5))))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
