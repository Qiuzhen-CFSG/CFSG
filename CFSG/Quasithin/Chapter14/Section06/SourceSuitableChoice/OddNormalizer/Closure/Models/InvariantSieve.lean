module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.F918
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.Contracts
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankOne
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.AlternatingBinary.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.MathieuTwentyTwo
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.BinaryAction
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# The cubic invariant component sieve

Apply the intrinsic Sylow-pair calculations to the actual F.9.18 list.
The rank-one, linear-three, G₂, alternating-seven and Mathieu rows are
excluded, including their central covers. The remaining symplectic row
has cyclic complement automizer. The binary-linear rows lift from the
central quotient and their genuine outer action identifies the full
Sylow join with Aut(PSL₄(2)) or Aut(PSL₅(2)).

InvariantSource applies this to the original strict closure and discharges
the cyclic-automizer exclusion using the original exchanged factors. The
quintic invariant case and the final source assembly remain with
qt-e-suitable-odd-normalizer. The explicit p=3 input
is owned by qt-e-14615-quintic-exclusion. No closure classification is
assumed or asserted by this sieve.
Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033, comparing
1.3.4 with F.9.18(4).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding Chapter1.XiEmbedding.InvariantThree
open Chapter13.Section08.Components.Models

private theorem symplectic_derived_pair
    {Q : Type*} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) {n : ℕ} (hn : 1 ≤ n)
    (hm : IsSp4DerivedAt (Q ⧸ center Q) (2 ^ n)) :
    PairReducible (S : Subgroup Q) R ∨
      (SymplecticModel 3 Q ∧ IsCyclic (pairAutomizer (S : Subgroup Q) R)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  by_cases hn2 : 2 ≤ n
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hp : ClassicalGroup.IsPSp (Q ⧸ center Q) 2 (2^n) :=
      ⟨F,inferInstance,inferInstance,hF,
        ⟨e.trans ((Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn2).trans
          Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv)⟩⟩
    rcases EvenRankTwo.rankTwo_of_source h (.symplectic n hn2 hp) with hr | ⟨_,hm,hc⟩
    · exact Or.inl hr
    · exact Or.inr ⟨hm,hc⟩
  · have hn1 : n = 1 := by omega
    have htwo : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
    exact Or.inl (AlternatingBinary.alternating_six h
      (e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix htwo)))

private theorem g2_derived_pair
    {Q : Type*} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) {n : ℕ} (hn : 1 ≤ n)
    (hm : IsG2DerivedAt (Q ⧸ center Q) (2 ^ n)) :
    PairReducible (S : Subgroup Q) R := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  by_cases hn2 : 2 ≤ n
  · have hp : ClassificationModels.IsG2At (Q ⧸ center Q) (2^n) :=
      ⟨F,inferInstance,inferInstance,hF,
        ⟨e.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega) hF)⟩⟩
    exact EvenRankTwo.ExceptionalActions.g2_pairReducible EvenRankTwo.source_g2TwoCenter h hn2 hp
  · have hn1 : n = 1 := by omega
    have htwo : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
    exact EvenRankTwo.SmallDerived.g2_pairReducible_of_equiv h
      (e.trans (Atlas.G2.DerivedEvenOrder.derivedFieldEquiv (Atlas.G2.binaryFieldEquiv htwo)))

/-- The F.9.18 list and the actual cubic Sylow pair leave precisely the
binary-linear groups or a symplectic group with cyclic pair automizer.
The rank-one, linear-three, G₂, A₇, and both M₂₂ cover rows are excluded. -/
theorem cubic_f918_pair_sieve
    {Q : Type*} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (hm : F918Models Q) :
    PairReducible (S : Subgroup Q) R ∨
      (SymplecticModel 3 Q ∧ IsCyclic (pairAutomizer (S : Subgroup Q) R)) ∨
      (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL Q n 2) := by
  rcases hm with ⟨hm,_⟩ | hm
  · cases hm with
    | bender hm => exact Or.inl (EvenRankOne.pairReducible_of_benderModel S R h hm)
    | linear_three n hn hm => exact Or.inl (EvenRankTwo.linear_reducible_of_source h hn hm)
    | symplectic n hn hm =>
      exact (symplectic_derived_pair h hn hm).imp_right Or.inl
    | g2 n hn hm => exact Or.inl (g2_derived_pair h hn hm)
    | linear_four hm => exact Or.inr (Or.inr ⟨4,Or.inl rfl,
        AlternatingBinary.binary_model AlternatingBinary.source_binaryMultiplierBound h (Or.inl rfl) hm⟩)
    | linear_five hm => exact Or.inr (Or.inr ⟨5,Or.inr rfl,
        AlternatingBinary.binary_model AlternatingBinary.source_binaryMultiplierBound h (Or.inr rfl) hm⟩)
    | alternating_seven he => exact Or.inl (AlternatingBinary.alternating_seven h he.some)
  · rcases hm with ⟨e⟩ | ⟨_,_,⟨e⟩⟩
    · obtain ⟨e⟩ := e
      let ec := QuotientGroup.congr (center Q) (center Sporadic.Mathieu.M22) e
        (Subgroup.center_map_equiv e)
      let ez := (QuotientGroup.quotientMulEquivOfEq Sporadic.Mathieu.m22_center_eq_bot).trans
        QuotientGroup.quotientBot
      exact Or.inl (SporadicRemaining.mathieu_twentyTwo_cover h (ec.trans ez))
    · exact Or.inl (SporadicRemaining.mathieu_twentyTwo_cover h e)

/-- The invariant component in the original local input has either cyclic
complement automizer or an actual binary-linear model and full Sylow-join
automorphism quotient. No model comparison or outer-action premise is assumed. -/
theorem invariant_cubic_f918_model
    {G : Type*} [Group G] [Finite G] {T X P J L : Subgroup G}
    (h : LocalInput 3 T X P J) (hsq : IsSQTK KnownSimple.IsKnownSimple J)
    (hT : IsSylowIn 2 T J) (hLJ : L ≤ J) (hn : (L.subgroupOf J).Normal)
    (hq : IsQuasisimple (XiQuotient L)) (hPL : P ≤ L) (hcomm : ⁅L,P⁆ = L)
    (hm : F918Models (XiQuotient L)) :
    (SymplecticModel 3 (XiQuotient L) ∧ IsCyclic (automizer T P)) ∨
      ((∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (XiQuotient L) n 2) ∧
        StrictInvariantModel T L L 3) := by
  have hTL : T ≤ normalizer L := (le_sup_right.trans h.overgroup).trans
    ((normal_subgroupOf_iff_le_normalizer hLJ).mp hn)
  obtain ⟨S,hS,hi⟩ := pairInput_of_sylow h hsq hT hLJ hn hq hPL hcomm
  rcases cubic_f918_pair_sieve hi hm with hr | ⟨hsym,hc⟩ | ⟨n,hn',hmodel⟩
  · exact (not_pairReducible h hPL hTL (by simpa only [hS] using hr)).elim
  · rw [hS] at hc
    exact Or.inl ⟨hsym,automizer_cyclic_of_pairAutomizer h hPL hTL hc⟩
  · have hXL := h.le_of_complement_le hPL
      ((normal_subgroupOf_iff_le_normalizer hLJ).mp hn)
    obtain ⟨ej⟩ := Chapter15.Section04.LocalSetup.EmbeddingReduction.BinaryAction.binary_quotient_aut_of_local
      h hT hLJ hn hXL hn' hmodel
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
    let : Fintype F := Fintype.ofFinite F
    let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
    let em := e.trans (Atlas.fieldEquivPSL n ef)
    exact Or.inr ⟨⟨n,hn',F,inferInstance,inferInstance,hF,⟨e⟩⟩,
      rfl,rfl,hTL,n,hn',⟨ej.trans (MulAut.congr em)⟩⟩
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
