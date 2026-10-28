module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionProjectiveModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionCovers
public import Theory.GroupTheory.PerfectRankTwoCoreInvolution
public import Theory.SpecificGroups.SL2.PrimeFieldOddSubgroups
public import Theory.Alternating.PrimeRank
public import Theory.Quasithin.CoprimeRank

/-!
# Excluding odd ternary containing groups for the order-32 A₆ section

The full normalizing Sylow and the ambient two-rank bound produce an
involution centralized by the perfect local component. The genuine cubic
cover of the ternary model lifts that component faithfully into prime-field
SL₂. Its cyclic Sylow three-subgroup contradicts the three-rank two of the
A₆ two-core quotient. The same argument covers both the projective and
special linear and unitary groups, retaining the original local component.

Source: Aschbacher–Smith A.3.12 and A.3.21, printed pp.47–48,55–56.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
open Chapter1.Section02.LocalModels

/-- The full Sylow-normalized order-32 A₆ local section cannot occur in
any of the odd prime ternary carriers, including their special covers. -/
theorem not_odd_ternary {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (B : Subgroup G) (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign G unitary 3 p ∨ IsSLSign G unitary 3 p) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsPerfect B := by
    let := hl.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  have hne : pCore 2 B ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hcore
    omega
  obtain ⟨z,_,hz,hBz⟩ := exists_involution_centralized_by_perfect_sup_sylow
    S B (odd_three_two_rank ho unitary hm) hn hne
  obtain ⟨residue,H,_,_,hR,f,hf,hc,h3⟩ := odd_three_cubic_carrier ho unitary hm
  obtain ⟨i,hi⟩ := rankThree_cubic_quotient_perfect_embedding hR f hf hc h3
    z hz B (le_sup_left.trans hBz)
  have hr : primeRank 3 B ≤ 1 := by
    let P : Sylow 3 B := Sylow.nonempty.some
    apply P.primeRank_le_one_of_isCyclic
    exact Matrix.SpecialLinearGroup.isCyclic_of_odd_pGroup_injective_primeField
      P.isPGroup' (by decide) (i.comp (P : Subgroup B).subtype)
      (hi.comp (P : Subgroup B).subtype_injective)
  have hr2 : primeRank 3 B = 2 := by
    rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup,
      primeRank_congr 3 hA6.some,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 (by decide) (by decide)]
  omega

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
