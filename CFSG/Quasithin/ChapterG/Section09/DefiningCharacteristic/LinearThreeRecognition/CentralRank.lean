module

public import Theory.GroupTheory.PrimeRankCentralCover
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank

/-!
# Automorphism-rank transport for actual central SL₃ quotients

A surjective central map SL₃(F) → L identifies their quotients by the
whole centers. Perfectness makes Aut(L) act faithfully on L/Z(L), giving
the required transport of a projective automorphism-rank bound. Over F₂
the existing exact projective calculation discharges that bound here.
For larger fields its proof remains with the PSL₃ automorphism-rank owner.

Source: Aschbacher--Smith, G.9.3, rank table on printed p.356.
-/

public section

open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

variable {F L : Type*} [Field F] [Finite F] [Group L] [Finite L]

/-- A central quotient retains an injection of its automorphism group into
the automorphism group of the actual projective SL₃ model. -/
theorem central_quotient_automorphism_rank_le
    (π : SL(3,F) →* L) (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ center SL(3,F)) :
    primeRank 2 (MulAut L) ≤ primeRank 2 (MulAut PSL(3,F)) := by
  let := Atlas.sl_perfect (F := F) 3 (by decide)
  let f : Cover SL(3,F) L := {
    toMonoidHom := π
    surjective := hπ
    isPerfect := inferInstance
    ker_le_center := hcentral }
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective hπ
  exact (automorphism_primeRank_le_quotient_center (E := L) 2).trans_eq
    (primeRank_equiv 2 (MulAut.congr f.quotientCenterEquiv.symm))

/-- The higher-field bound is reduced to the separately owned projective
automorphism calculation, with the given central map retained. -/
theorem central_quotient_automorphism_two_rank_le
    (π : SL(3,F) →* L) (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ center SL(3,F)) {n : ℕ}
    (hr : primeRank 2 (MulAut PSL(3,F)) ≤ 2 * n) :
    primeRank 2 (MulAut L) ≤ 2 * n :=
  (central_quotient_automorphism_rank_le π hπ hcentral).trans hr

/-- The smallest-field rank upper bound needs no automorphism premise. -/
theorem central_quotient_automorphism_two_rank_le_of_card_two
    (π : SL(3,F) →* L) (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ center SL(3,F)) (hF : Nat.card F = 2) :
    primeRank 2 (MulAut L) ≤ 2 := by
  exact (central_quotient_automorphism_rank_le π hπ hcentral).trans_eq
    (Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two F hF)

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
