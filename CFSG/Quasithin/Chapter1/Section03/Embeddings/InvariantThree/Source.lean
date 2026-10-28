module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.AlternatingBinary.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankOne
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.RankOne
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Source

/-!
# The complete intrinsic p=3 invariant-component sieve

The original local input and genuine Sylow subgroup construct the literal
Sylow pair in L/O₂(L). The full Theorem C model list is dispatched to the
proved pair calculations, including their actual central-cover and actor
transports. Irreducibility excludes each reducible pair. The surviving
planes give the linear, symplectic and exceptional alternatives; the actual
Held plane is retained as the adequate additional alternative.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528),
and the Held correction recorded in docs/quasithin-proof-basis.md.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.Source
open ClassificationModels
universe u

/-- Every genuine Theorem C component model satisfies the adequate intrinsic
p=3 conclusion on the original local input. No family or cover premise remains. -/
theorem alternatives_of_local_input {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {T X P H L : Subgroup G}
    (h : LocalInput 3 T X P H) (hH : IsSQTK κ H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hq : IsQuasisimple (XiQuotient L)) (hPL : P ≤ L) (hcomm : ⁅L, P⁆ = L)
    (hm : Section02.LocalModels.TheoremCModel
      (XiQuotient L ⧸ center (XiQuotient L))) :
    Alternatives 3 T P L ∨ HeldAlternative 3 T P L := by
  have hTL : T ≤ normalizer L := (le_sup_right.trans h.overgroup).trans
    ((normal_subgroupOf_iff_le_normalizer hLH).mp hLn)
  obtain ⟨S, hS, hi⟩ := pairInput_of_sylow h hH hT hLH hLn hq hPL hcomm
  have hn : ¬ PairReducible (S : Subgroup (XiQuotient L)) (quotientImage L P) := by
    intro hr
    exact not_pairReducible h hPL hTL (by simpa only [hS] using hr)
  cases hm with
  | alternating n hn hm =>
      exact Or.inl (AlternatingBinary.alternatives_of_local_input
        h hH hT hLH hLn hq hPL hcomm (Or.inl ⟨n, hn, hm⟩))
  | linear_odd p e hp ho he hs hm =>
      exact (hn (OddClassical.reducible_of_psl_two_odd hi hp ho he hs hm)).elim
  | three_odd p hp ho unitary hm =>
      cases unitary with
      | false => exact Or.inl (OddClassical.LinearThree.of_local_input
          h hH hT hLH hLn hq hPL hcomm hp ho hm)
      | true => exact (OddClassical.UnitaryThree.not_model_of_local_input
          h hH hT hLH hLn hq hPL hcomm hp ho hm).elim
  | rank_one hm => exact (hn (EvenRankOne.pairReducible_of_benderModel _ _ hi hm)).elim
  | rank_two hm => exact Or.inl (EvenRankTwo.alternatives_of_local_input
      h hH hT hLH hLn hq hPL hcomm hm)
  | binary_linear n hn hm =>
      exact Or.inl (AlternatingBinary.alternatives_of_local_input
        h hH hT hLH hLn hq hPL hcomm (Or.inr ⟨n, hn, hm⟩))
  | sporadic name hne hm =>
      have hs := SporadicRemaining.Source.alternatives_of_local_input
        h hH hT hLH hLn hq hPL hcomm
      cases name with
      | j3 => exact (hne rfl).elim
      | j4 => exact (hn (SporadicActions.j4_pairReducible hi hm.some)).elim
      | m11 => exact hs (Or.inl (Or.inl hm))
      | m12 => exact hs (Or.inl (Or.inr (Or.inl hm)))
      | m22 => exact hs (Or.inl (Or.inr (Or.inr (Or.inl hm))))
      | m23 => exact hs (Or.inr (Or.inl hm))
      | m24 => exact hs (Or.inr (Or.inr (Or.inl hm)))
      | j2 => exact hs (Or.inr (Or.inr (Or.inr hm)))
      | hs => exact hs (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hm)))))
      | he => exact hs (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))))
      | ru => exact hs (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))))
  | janko_one hm =>
      exact SporadicRemaining.Source.alternatives_of_local_input
        h hH hT hLH hLn hq hPL hcomm
        (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm)))))))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.Source
