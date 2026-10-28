module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.AlternatingBinary
public import Theory.Alternating.OddCentralCovers
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient

/-!
# Original alternating and binary-linear intrinsic three-complement branches

The actual A₈–PSL₄(2) comparison transfers the proved nonexceptional
alternating cover bound, and the faithful PSL₅(2) presentation gives trivial
covering center. These discharge the multiplier premise of the existing
A₅–A₈ and PSL₄(2)/PSL₅(2) pair sieve. Its actual intrinsic consumer retains
the genuine Sylow hypothesis and transports the plane and whole-group model.

Source: Aschbacher–Smith, Proposition 1.3.4 and I.1.3, printed pp.511,407.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.AlternatingBinary
universe u

/-- The earlier covering bounds for both binary-linear survivors are proved. -/
theorem source_binaryMultiplierBound : BinaryMultiplierBound.{u} := by
  intro K _ _ hK n hn hm
  let : IsQuasisimple K := hK
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  rcases hn with rfl | rfl
  · let _ := Fintype.ofFinite F
    let eF : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
    let ea := e.trans ((Atlas.fieldEquivPSL 4 eF).trans
      Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)
    exact GLS3.Chapter5.OddCentralCovers.center_card_dvd_two_of_nonexceptional
      8 (by decide) (by decide) (by decide) ea
  · have hz := PerfectCentralCovering.center_eq_bot_of_centralQuotientEquiv
      (Theory.SpecificGroups.PSL5Two.UniversalCover.field_universalProjection_ker_eq_bot F hF) e
    simp only [hz, card_bot, one_dvd]

/-- All alternating and binary-linear pair branches, with no multiplier premise. -/
theorem alternative_of_source
    {Q : Type u} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R)
    (hm : (∃ n : ℕ, (5 ≤ n ∧ n ≤ 8) ∧ Section02.LocalModels.IsAlternating (Q ⧸ center Q) n) ∨
      ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (Q ⧸ center Q) n 2) :
    PairReducible (S : Subgroup Q) R ∨
      (Nonempty (R ≃* Plane 3) ∧ ExceptionalModel Q) :=
  alternating_or_binary source_binaryMultiplierBound h hm

/-- The source local/Sylow input gives the literal intrinsic alternatives. -/
theorem alternatives_of_local_input {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {T X P H L : Subgroup G}
    (h : LocalInput 3 T X P H) (hH : IsSQTK κ H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hq : IsQuasisimple (XiQuotient L)) (hPL : P ≤ L) (hcomm : ⁅L, P⁆ = L)
    (hm : (∃ n : ℕ, (5 ≤ n ∧ n ≤ 8) ∧ Section02.LocalModels.IsAlternating
      (XiQuotient L ⧸ center (XiQuotient L)) n) ∨ ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      ClassicalGroup.IsPSL (XiQuotient L ⧸ center (XiQuotient L)) n 2) :
    Alternatives 3 T P L := by
  have hTL : T ≤ normalizer L := (le_sup_right.trans h.overgroup).trans
    ((normal_subgroupOf_iff_le_normalizer hLH).mp hLn)
  obtain ⟨S, hS, hi⟩ := pairInput_of_sylow h hH hT hLH hLn hq hPL hcomm
  rcases alternative_of_source hi hm with hr | ⟨he, hm⟩
  · exact (not_pairReducible h hPL hTL (by simpa only [hS] using hr)).elim
  · exact ⟨plane_of_quotient_plane h hPL he, Or.inr ⟨hTL, Or.inr (Or.inr ⟨rfl, hm⟩)⟩⟩
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.AlternatingBinary
