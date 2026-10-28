module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryCenterRank
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Alternating.Centers
public import Theory.Alternating.PrimeRank
public import Theory.Alternating.OddCentralCovers
public import Theory.Alternating.proposition_5_2_9_10
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.Mathieu.SchurMultipliers.M12Upper
public import Theory.SpecificGroups.PSL4Two.SchurMultiplier

/-!
# Small ordinary central quotients cannot contain the original elementary 64

The exact alternating multiplier bounds and native two-rank bounds force
the elementary kernel intersection to have at most two elements. Its image
also has at most sixteen elements, contradicting the original order 64.
The M12 argument uses its proved perfect-cover kernel bound directly.

Source: Aschbacher--Smith 12.7.5, printed p.840; the concrete multiplier
and rank calculations retain their source attribution in their owner modules.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section07
variable {B : Type*} [Group B] [Finite B] [IsQuasisimple B]

/-- No ordinary alternating quotient of degree at most eight admits the
original elementary subgroup of order 64 in its quasisimple cover. -/
theorem original_point_ordinary_not_alternating
    (U : Subgroup B) [IsElementaryAbelian 2 U] (hU : Nat.card U = 64)
    {n : ℕ} (hn : n ≤ 8) (e : B ⧸ center B ≃* alternatingGroup (Fin n)) : False := by
  have h5 := Chapter1.QuasisimpleInvolutions.Alternating.five_le_degree e
  have hd : Nat.card (center B) ∣ 6 := by
    by_cases he : n = 6 ∨ n = 7
    · exact GLS3.Chapter5.exceptional_alternating_center_card_dvd_six n e he
    · exact (GLS3.Chapter5.OddCentralCovers.center_card_dvd_two_of_nonexceptional
        n h5 (fun hh => he (.inl hh)) (fun hh => he (.inr hh)) e).trans (by decide)
  have hr : primeRank 2 (alternatingGroup (Fin n)) ≤ 4 := by
    rw [(GLS3.Chapter5.PRank.alternating_hasPRank_two n).primeRank_eq Nat.prime_two]
    omega
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hq : q.ker = center B := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hbig := original_point_four_le_card_kernel U hU q hr
  rw [hq] at hbig
  have h64 : Nat.card (U ⊓ center B : Subgroup B) ∣ 64 :=
    hU ▸ card_dvd_of_le (inf_le_left : U ⊓ center B ≤ U)
  have h6 : Nat.card (U ⊓ center B : Subgroup B) ∣ 6 :=
    (card_dvd_of_le (inf_le_right : U ⊓ center B ≤ center B)).trans hd
  have h2 : Nat.card (U ⊓ center B : Subgroup B) ∣ 2 :=
    (show Nat.gcd 64 6 = 2 by decide) ▸ Nat.dvd_gcd h64 h6
  have hsmall := Nat.le_of_dvd (by decide : 0 < 2) h2
  omega

/-- The binary degree-four quotient is the actual alternating-eight row. -/
theorem original_point_ordinary_not_psl_four_two
    (U : Subgroup B) [IsElementaryAbelian 2 U] (hU : Nat.card U = 64)
    (hm : ClassicalGroup.IsPSL (B ⧸ center B) 4 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact original_point_ordinary_not_alternating U hU (by decide : 8 ≤ 8)
    (e.trans (Matrix.PSL4Two.binaryEquivAlternatingEight F hF))

/-- The native M12 quotient and its whole covering kernel are too small
in elementary rank for the original unchanged module. -/
theorem original_point_ordinary_not_m12
    (U : Subgroup B) [IsElementaryAbelian 2 U] (hU : Nat.card U = 64)
    (e : B ⧸ center B ≃* Sporadic.Mathieu.M12) : False := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hq : q.ker = center B := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let c : PerfectCentralCovering.Cover B Sporadic.Mathieu.M12 := {
    toMonoidHom := q
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := hq.le }
  have hb := Sporadic.Mathieu.SchurMultipliers.m12_cover_kernel_card_le_two c
  change Nat.card q.ker ≤ 2 at hb
  have hbig := original_point_four_le_card_kernel U hU q
    (Sporadic.Mathieu.m12_twoRank_le_three.trans (by decide : 3 ≤ 4))
  have hsmall := (Nat.card_le_card_of_injective
    (inclusion (inf_le_right : U ⊓ q.ker ≤ q.ker)) (inclusion_injective _)).trans hb
  omega

end CFSG.Quasithin.Chapter12.Section07
