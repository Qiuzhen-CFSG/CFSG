module

public import Theory.SpecificGroups.Held.TwoRank.Normalizer
public import Theory.GroupTheory.PrimeRankCentralCover

/-!
# The Held automorphism-rank input to G.7

The concrete extension of the actual Held Sylow subgroup has two-rank at
most six, including elementary subgroups meeting the outside coset. The
independent full-normalizer quotient bound and automorphism-realization
theorem transfer that calculation to all abstract automorphisms. Faithful
descent then gives the same bound for every perfect central cover whose
literal quotient by its whole center is isomorphic to the Held carrier.

The two producer premises remain explicit here until their existing owners
complete them; these conditional reductions do not assert the completed
source bound. Neither a rank premise nor a model-identification premise is
used for the concrete extension calculation.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the discarded
Held case of G.7.3(2), printed p.348 (PDF p.359). The separate degree-twenty
input from G.7.2(6) is in `SporadicLocal.OddSubgroups`.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section07.SporadicLocal
open Subgroup Theory.GroupTheory

/-- The source rank bound, conditional only on the two existing outer-group producers. -/
theorem he_automorphism_twoRank_le_six_of_normalizer
    (hquot : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom) :
    primeRank 2 (MulAut Held.He) ≤ 6 := by
  let e := MulEquiv.ofBijective Held.permutationGroup.normalizerMonoidHom
    ⟨Held.OuterInvolution.normalizer_action_injective, hreal⟩
  rw [← primeRank_equiv 2 e]
  exact Held.TwoRank.normalizer_twoRank_le_six hquot

/-- The same source bound for a perfect central cover, using its actual central quotient. -/
theorem he_centralQuotient_automorphism_twoRank_le_six_of_normalizer
    (hquot : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* Held.He) : primeRank 2 (MulAut L) ≤ 6 := by
  have h := automorphism_primeRank_le_quotient_center (E := L) 2
  rw [primeRank_equiv 2 (MulAut.congr e)] at h
  exact h.trans (he_automorphism_twoRank_le_six_of_normalizer hquot hreal)

end CFSG.Quasithin.ChapterG.Section07.SporadicLocal
