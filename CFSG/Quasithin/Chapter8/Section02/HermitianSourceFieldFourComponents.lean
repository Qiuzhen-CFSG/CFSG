module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourOuter
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianParabolics
public import Theory.GroupTheory.PrimeRankAutomorphismOrder
import all CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianParabolics
import all Theory.SpecificGroups.SymplecticSix.BinarySylowAutomorphisms

/-!
# Containing components for the field-four Hermitian residual

Retain the literal inclusion of the original perfect residual and its
nonzero fully moved two-core module. Its PSL₃(4) quotient has order 20160;
this replaces the rank-twelve hypothesis used for larger Hermitian fields
in excluding the small relative-rank-two models. The actual quotient map
normalizes a nontrivial two-group, so the existing full-parabolic exclusions
remove all remaining Lie-type rows, including the two unitary rows and Ree.

The nine-space also excludes Sp₆(2): its explicit nonabelian Sylow of order
512 has elementary rank at most eight. Together with the complete Theorem B
rank sieve, this leaves an actual J₄ central quotient. No SQTK condition is
imposed on the odd normalizer. The Chapter 12 FieldFourComponents consumer
applies this result to the normal component selected by residual uniqueness.
J₄ exclusion, hence whole-normalizer control, remains a separate step.
Source: Aschbacher--Smith 4.4.11--12, printed pp.621--623, used in 8.2.7,
printed p.718, refs/quasithin.pdf. The coordinate Sylow calculation reuses
the existing attributed SymplecticSix carrier, without finite enumeration.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open Chapter4.Section04.NormalizedRankOneOddControl Chapter7.NormalizedSource.NonMathieuHermitian
open ChapterA.Section02 ClassificationModels
open Theory.SpecificGroups

private theorem binary_symplectic_six_rank_le_eight
    {Q : Type*} [Group Q] [Finite Q] (hm : ClassicalGroup.IsPSp Q 3 2) :
    primeRank 2 Q ≤ 8 := by
  open SymplecticSix.BinarySylowAutomorphisms in
  have hr : primeRank 2 Parameters ≤ 8 := by
    apply primeRank_le_of_noncommutative_card_prime_pow (by simpa using card_parameters)
    intro h
    let := h
    let x : Parameters := ⟨![1,0,0,0,0,0,0,0,0]⟩
    let y : Parameters := ⟨![0,0,1,0,0,0,0,0,0]⟩
    have hh := congrArg (fun z : Parameters => z.val 1) (mul_comm x y)
    change (1 : ZMod 2) = 0 at hh
    exact one_ne_zero hh
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let a := (e.trans (SymplecticSix.pspFieldEquivZModTwo F hF)).trans
    SymplecticSix.EvenProjective.equiv.symm
  rw [primeRank_congr 2 a,SymplecticSix.BinarySylowAutomorphisms.sylow.primeRank_eq,
    ←primeRank_congr 2 SymplecticSix.BinarySylowAutomorphisms.sylowEquiv]
  exact hr

private theorem field_four_unitary_five_or_ree
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    (F K W : Subgroup G) [Group.IsPerfect F]
    (hFK : F ≤ K) (hWF : W ≤ F.pCoreIn 2) (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : F →* S) (hπ : Function.Surjective π)
    (hcardS : Nat.card S = 20160)
    {n : ℕ} (hm : IsRankTwoModel (K ⧸ center K) n) :
    UnitaryFiveOrReeModel (K ⧸ center K) := by
  let r := residualQuotientMap hFK (MulEquiv.refl (K ⧸ center K))
  let := residualQuotientMap_kernel_solvable hFK (MulEquiv.refl (K ⧸ center K))
  have hd : 20160 ∣ Nat.card (K ⧸ center K) := by
    rw [←hcardS]
    exact SimpleSection.card_dvd_of_solvable_representation hS π hπ r
  cases hm with
  | linear hn hm =>
    exfalso
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hcard)
    have hn2 : 2 ≤ n := by
      by_contra h
      have he : n = 1 := by omega
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hcard,he] at hd
      norm_num at hd
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm e
    exact no_linear_three_local hS hexp π hπ hn2 hcard _ hp hpne r hnorm
  | unitary_four hn hm =>
    exfalso
    obtain ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    let : CharP E 2 := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.charP_two
      n (by omega) hcard
    obtain ⟨a⟩ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
      J n (by omega) hcard hconj
    let t := e.trans a
    let r := residualQuotientMap hFK t
    let := residualQuotientMap_kernel_solvable hFK t
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm t
    exact no_unitary_four_local hS hexp π hπ J.conj J.conj_involutive
      n (by omega) hcard hconj _ hp hpne r hnorm
  | unitary_five hn hm => exact Or.inl (by simpa only [hn,show 2 ^ 2 = 4 from rfl] using hm)
  | symplectic hn hm =>
    exfalso
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : CharP E 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := E)).symm
    let r := residualQuotientMap hFK a
    let := residualQuotientMap_kernel_solvable hFK a
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm a
    exact no_symplectic_four_local hS hexp π hπ _ hp hpne r hnorm
  | g2 hn hm =>
    exfalso
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hcard)
    have hbig : 2 < Nat.card E := by
      rw [hcard]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) hn)
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm e
    exact no_g2_local hS hexp π hπ hbig _ hp hpne r hnorm
  | triality hn hm =>
    exfalso
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n (by omega)).mp hm
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm e
    exact no_triality_local hS hexp π hπ n (show 0 < n from hn) _ hp hpne r hnorm
  | ree_f4 m hm _ he => exact Or.inr ⟨m,hm,he⟩
  | symplectic_derived _ he =>
    exfalso
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hd
    have hd' := hd.trans (commutator (ClassicalGroup.PSp 2 (ZMod 2))).card_subgroup_dvd_card
    rw [← Nat.card_congr
      (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := ZMod 2)).toEquiv,
      Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two] at hd'
    norm_num at hd'
  | g2_derived _ he =>
    exfalso
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hd
    have hd' := hd.trans (commutator (Atlas.G2.Model (ZMod 2))).card_subgroup_dvd_card
    rw [Atlas.G2.card_Model,Nat.card_zmod] at hd'
    norm_num at hd'
  | tits _ he =>
    exfalso
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv,Tits.parrottGroup_card] at hd
    norm_num at hd


/-- The field-four quotient excludes every relative-rank-two containing component. -/
theorem field_four_no_rankTwo_residual
    {G S E : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    [Field E] [Finite E] [CharP E 2]
    (F K W : Subgroup G) [Group.IsPerfect F]
    (hFK : F ≤ K) (hWF : W ≤ F.pCoreIn 2) (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (hS : ¬ Group.IsSolvable S) (e : S ≃* PSL(3,E)) (hc : Nat.card E = 4)
    (π : F →* S) (hπ : Function.Surjective π)
    {n : ℕ} (hm : IsRankTwoModel (K ⧸ center K) n) : False := by
  have hsquare : Nat.card E = 2^(2*1) := by simpa using hc
  have hexp := Matrix.PSL3.LinearThree.not_two_exponent e hsquare
  have hthree := Matrix.PSL3.LinearThree.square_three_dvd_card e hsquare
  have hseven := Matrix.PSL3.LinearThree.square_seven_dvd_card e hsquare
  have hcardS : Nat.card S = 20160 := by
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hc]
    norm_num
  rcases field_four_unitary_five_or_ree F K W hFK hWF hne hcomm
    hS hexp π hπ hcardS hm with h | ⟨m,hm,⟨a⟩⟩
  · obtain ⟨E',_,_,J,hcard,hconj,⟨a⟩⟩ := h
    have hcard' : Nat.card E' = 16 := hcard
    let := SymplecticFour.EvenProjective.charTwo_of_card (show Nat.card E' = 2^4 by simpa using hcard')
    obtain ⟨b⟩ := UnitaryFive.projective_equiv_identity_four J hcard' hconj
    let t := a.trans b
    let r := residualQuotientMap hFK t
    let := residualQuotientMap_kernel_solvable hFK t
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm t
    exact no_seven_unitary_five_local hS hseven π hπ
      (HermitianForm.IdentityGram.identityGram J) hcard' hconj rfl _ hp hpne r hnorm
  · let r := residualQuotientMap hFK a
    let := residualQuotientMap_kernel_solvable hFK a
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm a
    exact no_ree_local_of_three_dvd hS hexp hthree π hπ hm _ hp hpne r hnorm

/-- A B-model component containing the original nine-space and perfect
field-four residual has an actual J₄ central quotient. -/
theorem field_four_containing_component_janko_four
    {G S E : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    [Field E] [Finite E] [CharP E 2]
    (F K W : Subgroup G) [Group.IsPerfect F]
    (hFK : F ≤ K) (hWF : W ≤ F.pCoreIn 2) (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (hS : ¬ Group.IsSolvable S) (e : S ≃* PSL(3,E)) (hc : Nat.card E = 4)
    (π : F →* S) (hπ : Function.Surjective π)
    (hr : 9 ≤ primeRank 2 (K ⧸ center K))
    (hm : IsTheoremBModel (K ⧸ center K)) :
    Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  rcases hm.remaining_of_twoRank_ge_eight (by omega) with ho | hb | ⟨n,hm⟩ | hsp | hj
  · exact (no_theoremB_odd_model_of_twoRank_ge_eight (by omega) ho).elim
  · exact (no_bender_of_residual_module K F W hFK hWF hne hcomm hb).elim
  · exact (field_four_no_rankTwo_residual F K W hFK hWF hne hcomm hS e hc π hπ hm).elim
  · have hh := binary_symplectic_six_rank_le_eight hsp
    omega
  · exact hj
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
