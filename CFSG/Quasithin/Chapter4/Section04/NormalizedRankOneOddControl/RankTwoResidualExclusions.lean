module

public import Theory.GroupTheory.ResidualCentralQuotientImage
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.BenderExclusion
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.UnitaryFourLocal
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# The remaining component rows after the original residual embedding

The residual's actual central-quotient representation excludes the PSL₃,
PSp₄, PSU₄, G₂ and triality parabolics. Rank twelve also removes the three small
derived endpoints. What remains is an actual PSU₅(4) or Ree model,
on the same component central quotient. This is a partial exclusion, not
the complete odd-normalizer theorem: the unitary and Ree local module
arguments and ambient residual uniqueness remain to be proved.

Source: the relative-rank-two branch of Aschbacher--Smith 4.4.12,
printed pp.621--622.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
open ClassificationModels

/-- The remaining rows, with actual projective or Ree isomorphism witnesses. -/
@[expose] def UnitaryFiveOrReeModel (Q : Type*) [Group Q] : Prop :=
  ClassicalGroup.IsPSU Q 5 4 ∨
  ∃ m : ℕ, 1 ≤ m ∧ Nonempty (Q ≃* ReeF4.Model m)

/-- Transport preserves the actual remaining model witnesses. -/
theorem UnitaryFiveOrReeModel.of_mulEquiv {Q R : Type*} [Group Q] [Group R]
    (h : UnitaryFiveOrReeModel Q) (e : R ≃* Q) : UnitaryFiveOrReeModel R := by
  rcases h with hq | ⟨m,hm,⟨a⟩⟩
  · exact Or.inl (hq.of_mulEquiv e)
  · exact Or.inr ⟨m,hm,⟨e.trans a⟩⟩

private theorem two_pow_twelve_dvd_of_rank {Q : Type*} [Group Q] [Finite Q]
    (hr : 12 ≤ primeRank 2 Q) : 4096 ∣ Nat.card Q := by
  by_contra hd
  have hb : primeRank 2 Q ≤ 11 := primeRank_le_of_prime_pow_not_dvd hd
  omega

/-- Applying all linear-Levi exclusions to the literal residual leaves only
the actual unitary and Ree component models. -/
theorem unitary_five_or_ree_of_residual_module
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    (F K W : Subgroup G) [Group.IsPerfect F]
    (hFK : F ≤ K) (hWF : W ≤ F.pCoreIn 2) (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : F →* S) (hπ : Function.Surjective π)
    (hr : 12 ≤ primeRank 2 (K ⧸ center K))
    {n : ℕ} (hm : IsRankTwoModel (K ⧸ center K) n) :
    UnitaryFiveOrReeModel (K ⧸ center K) := by
  have hd := two_pow_twelve_dvd_of_rank hr
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

/-- The remaining configuration keeps every embedding and centralizer clause
of the rank-two component reduction. -/
@[expose] def UnitaryFiveOrReeComponentCase {G : Type*} [Group G]
    (L V A : Subgroup G) (S : Type*) [Group S] : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧ UnitaryFiveOrReeModel (K ⧸ center K) ∧
    V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    12 ≤ primeRank 2 (K ⧸ center K) ∧
    ∃ U : Subgroup (K ⧸ center K), ∃ f : U →* S, Function.Surjective f

/-- Literal consumer: the original module and residual remove the linear-Levi
rows from the component constructed by residual uniqueness. -/
theorem unitary_five_or_ree_component_of_rankTwo_case
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    {L W A : Subgroup G}
    (hWF : W ≤ (oddActorResidual L A).pCoreIn 2) (hne : W ≠ ⊥)
    (hcomm : W = ⁅W,oddActorResidual L A⁆)
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : oddActorResidual L A →* S) (hπ : Function.Surjective π)
    (hc : RankTwoComponentCase L W A S) : UnitaryFiveOrReeComponentCase L W A S := by
  obtain ⟨K,hK,hn,hout,hcore,⟨n,hm⟩,hw,hf,hcent,hr,hsection⟩ := hc
  let N := normalizer (A : Set G)
  let J := K.map N.subtype
  let e : J ≃* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  let z : (J ⧸ center J) ≃* (K ⧸ center K) := QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
  let : Group.IsPerfect (oddActorResidual L A) := oddActorResidual_isPerfect L A
  have hrJ : 12 ≤ primeRank 2 (J ⧸ center J) := by
    rwa [primeRank_equiv 2 z]
  have hu := unitary_five_or_ree_of_residual_module (oddActorResidual L A) J W
    hf hWF hne hcomm hS hexp π hπ hrJ (hm.of_mulEquiv z)
  exact ⟨K,hK,hn,hout,hcore,hu.of_mulEquiv z.symm,hw,hf,hcent,hr,hsection⟩

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
