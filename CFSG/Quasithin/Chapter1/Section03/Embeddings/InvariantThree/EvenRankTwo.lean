module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Automizer
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Carriers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Symplectic
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.ExceptionalActions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Ree
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.SmallDerived
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.AlternatingBinary.Six

/-!
# The characteristic-two rank-two three-complement sieve

For a genuine Sylow pair, the complement has three-rank two and its product
with the Sylow two-subgroup is a proper solvable subgroup. The exported
reductions exclude containment in a rank-one parabolic and convert an abelian
complement into the elementary plane. The pair stabilizer maps onto the pair
automizer, whose cyclicity follows from a cyclic outer group only after the
inner kernel has been shown to centralize the complement.

The carrier comparisons retain the full symplectic matrix group, the even
field degree and the mod-three restriction. They also identify the actual
PSp4(2)' constructor with A6 using the existing polar representation.

`rankTwo` assembles all eight constructors of `RankTwoTheoremC`. The binary
linear, G₂ and genuine triality branches use their proved placement and
field/graph action calculations. General Ree uses the actual `LocalBlockInput`
and the three-free Borel obstruction. The small derived G₂ and Tits branches
use the proper-parabolic obstruction; PSp₄(2)' passes through its actual A₆
isomorphism. The surviving symplectic branch identifies the full matrix
carrier and proves cyclicity of the whole pair automizer.

Only the explicitly named universal multiplier implications of I.1.3 remain
parameters. They concern perfect central covers independently of the Sylow
pair; no placement, action or local sieve conclusion is assumed.
`symplectic_of_localInput` applies the sieve to the literal quotient L/O₂(L),
rules out reducibility using the source normalizer action, and transports
the plane and cyclicity back to P and Aut_T(P). The surrounding Theorem C
classification and the earlier multiplier results remain with the parent
source-theorem assembly.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`), and
I.1.1–I.1.3, printed p.407 (PDF p.418).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo
universe u

variable
  (hlinear : ∀ f : ℕ, 1 ≤ f → ∀ (F : Type) [Field F] [Finite F],
    Nat.card F = 2 ^ f → Linear.Placement.ScalarCover.UniversalMultiplierInput F f)
  (hsymplectic : SymplecticCentralKernelTheorem.{u})
  (hg2 : ExceptionalActions.G2TwoCenter.{u})
  (htriality : ExceptionalActions.TrialityTwoCenter.{u})

include hlinear hsymplectic hg2 htriality

/-- The full characteristic-two rank-two sieve, retaining only universal
earlier multiplier inputs. Every model is identified by an actual isomorphism,
and reducibility concerns every two-subgroup of the full pair automizer. -/
theorem rankTwo {Q : Type u} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (hmodel : Section02.LocalModels.RankTwoTheoremC (Q ⧸ center Q)) :
    PairReducible (S : Subgroup Q) R ∨
      (Nonempty (R ≃* Plane 3) ∧ SymplecticModel 3 Q ∧
        IsCyclic (pairAutomizer (S : Subgroup Q) R)) := by
  cases hmodel with
  | linear f hf hm =>
      exact Or.inl (Linear.pairReducible_of_universalMultiplierInput h hf hm
        (hlinear f hf))
  | symplectic f hf hm => exact symplectic_case hsymplectic h hf hm
  | g2 f hf hm => exact Or.inl (ExceptionalActions.g2_pairReducible hg2 h hf hm)
  | triality f hf hm =>
      exact Or.inl (ExceptionalActions.triality_pairReducible htriality h hf hm)
  | ree m hm he => exact Or.inl (Ree.pairReducible_of_equiv hm h he)
  | symplectic_derived he =>
      obtain ⟨e⟩ := symplectic_derived_is_alternating_six he
      exact Or.inl (AlternatingBinary.alternating_six h e)
  | g2_derived he =>
      obtain ⟨e⟩ := he
      exact Or.inl (SmallDerived.g2_pairReducible_of_equiv h e)
  | tits he =>
      obtain ⟨e⟩ := he
      exact Or.inl (SmallDerived.tits_pairReducible_of_equiv h e)

/-- The rank-two branch in the actual component quotient of the source setup.
Relative normality in H and genuine Sylow membership supply the pair; the
original irreducible normalizer action eliminates its reducible alternative.
The conclusion retains the full symplectic carrier, even field degree and
mod-three restriction, and cyclicity of the original Aut_T(P). -/
theorem symplectic_of_localInput {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {T X P H L : Subgroup G}
    (h : LocalInput 3 T X P H) (hH : IsSQTK κ H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hq : IsQuasisimple (XiQuotient L)) (hPL : P ≤ L) (hcomm : ⁅L, P⁆ = L)
    (hmodel : Section02.LocalModels.RankTwoTheoremC
      (XiQuotient L ⧸ center (XiQuotient L))) :
    Nonempty (P ≃* Plane 3) ∧ SymplecticModel 3 (XiQuotient L) ∧
      IsCyclic (automizer T P) := by
  have hTL : T ≤ normalizer L := (le_sup_right.trans h.overgroup).trans
    ((normal_subgroupOf_iff_le_normalizer hLH).mp hLn)
  obtain ⟨S, hS, hpair⟩ := pairInput_of_sylow h hH hT hLH hLn hq hPL hcomm
  rcases rankTwo hlinear hsymplectic hg2 htriality hpair hmodel with hred | hs
  · rw [hS] at hred
    exact (not_pairReducible h hPL hTL hred).elim
  · obtain ⟨he, hm, hc⟩ := hs
    rw [hS] at hc
    exact ⟨plane_of_quotient_plane h hPL he, hm,
      automizer_cyclic_of_pairAutomizer h hPL hTL hc⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo
