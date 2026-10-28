module
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.SylowCoverage
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Candidate
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.PrimeRankOrderBound

/-!
# Automorphism two-rank of the native Mathieu group

Sylow conjugacy and the checked elementary-subgroup coverage bound every
elementary subgroup of M₂₄ by 64. Its proved automorphism innerness transfers
that bound to Aut(M₂₄), using centerlessness inherited from a source quotient.
The six-dimensional point-component section consumes this exact bound.
Source: Aschbacher--Smith H.14.1 and 10.2.9, pp.396--397,750--751.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu
open M24ChapterHStabilizers.ElementaryFusion M24LocalGeometry

/-- Every native elementary subgroup has order at most 64. -/
theorem m24_elementary_card_le_sixtyfour (E : Subgroup M24) [IsElementaryAbelian 2 E] :
    Nat.card E ≤ 64 := by
  obtain ⟨S,hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 S SextetCore.nativeSylow
  let a := MulAut.conj g
  let U := E.map a.toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map a.toMonoidHom
  have hUP : U ≤ SylowNormalizer.candidate := by
    have h := map_mono (f := a.toMonoidHom) hES
    change U ≤ (g • S : Sylow 2 M24) at h
    rwa [hg] at h
  have hc : Nat.card U = Nat.card E := card_map_of_injective a.injective
  by_cases hu : 32 ≤ Nat.card U
  · rcases large_elementary_le_candidate U hu hUP with h | h | ⟨i,h⟩
    · have hh := card_le_of_le h
      rw [candidate_card, hc] at hh
      exact hh
    · have hh := card_le_of_le h
      rw [candidate_card, hc] at hh
      exact hh
    · have hh := (card_le_of_le h).trans (smallCandidate_card_le i)
      rw [hc] at hh
      omega
  · omega

/-- Innerness transfers the native elementary bound to all automorphisms. -/
theorem m24_automorphism_rank_le_six (hz : center M24 = ⊥) :
    primeRank 2 (MulAut M24) ≤ 6 := by
  let e : M24 ≃* MulAut M24 := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot hz,M24OuterRestriction.conj_surjective⟩
  rw [←primeRank_equiv 2 e]
  apply (primeRank_le_iff_elementary_card_le M24).mpr
  intro E hE
  let := hE
  exact m24_elementary_card_le_sixtyfour E
end Sporadic.Mathieu
