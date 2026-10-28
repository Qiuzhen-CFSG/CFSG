module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerComplete
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.LocalModels

/-!
# Local component exclusions for the degree-four doubled orbit

The original fixed residual has quotient L₄(2). After passage to a containing
component's central quotient its kernel is a two-group, so its perfect image
retains cubic rank two and all three odd primes 3, 5 and 7. The original seed
has nontrivial image normalized by this perfect subgroup. Actual parabolic
bounds exclude every Bender and characteristic-two rank-two model. The full
rank-eight B-list consequently leaves Sp₆(2) and J₄, before the separate outer
and pushing-up arguments. No model name substitutes for a group equivalence.

Source: Aschbacher--Smith 4.4.10--12 and 12.1.9(1), pp.621--623,793.
NormalizerFourPlacement constructs these data from the literal residual and
applies this exclusion to the original odd-normalizer obstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
open ClassificationModels
variable {Q : Type*} [Group Q] [Finite Q]

/-- The actual local image retains the three odd prime divisors of L₄(2). -/
@[expose] def FourComponentLocalData (Q : Type*) [Group Q] : Prop :=
  ∃ B P : Subgroup Q, Group.IsPerfect B ∧ 2 ≤ primeRank 3 B ∧
    IsPGroup 2 P ∧ P ≠ ⊥ ∧ B ≤ normalizer (P : Set Q) ∧ P ≤ B ∧ 105 ∣ Nat.card B

/-- Transport both literal subgroups and their normalization. -/
theorem FourComponentLocalData.of_mulEquiv {S : Type*} [Group S]
    (h : FourComponentLocalData Q) (e : Q ≃* S) : FourComponentLocalData S := by
  let : Finite S := Finite.of_equiv Q e.toEquiv
  obtain ⟨B,P,hB,hr,hP,hne,hn,hPB,hd⟩ := h
  let := hB
  refine ⟨B.map e.toMonoidHom,P.map e.toMonoidHom,Group.IsPerfect.map _,
    ?_,hP.map _,?_,(map_mono hn).trans (P.le_normalizer_map e.toMonoidHom),map_mono hPB,?_⟩
  · exact hr.trans_eq (primeRank_equiv 3 (e.subgroupMap B))
  · exact fun he => hne ((map_eq_bot_iff_of_injective P e.injective).mp he)
  · rwa [card_map_of_injective e.injective]

private theorem no_local_of_rank_le_one (h : FourComponentLocalData Q)
    (hr : primeRank 3 Q ≤ 1) : False := by
  obtain ⟨B,_,_,hb,_,_,_⟩ := h
  have := (primeRank_subgroup_le 3 B).trans hr
  omega

/-- Every Bender row is incompatible with the actual placed residual. -/
theorem FourComponentLocalData.not_bender (h : FourComponentLocalData Q) :
    ¬ IsBenderModel Q := by
  intro hm
  cases hm with
  | linear n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    apply no_local_of_rank_le_one h
    rw [primeRank_equiv 3 (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm)]
    exact Matrix.SL2.binary_odd_primeRank_le_one (by decide)
  | unitary n hn hm =>
    obtain ⟨B,P,hB,hr,hP,hne,hN,hPB,_⟩ := h
    let := hB
    let : Group.IsSolvable (normalizer (P : Set Q)) :=
      ChapterF.Source.Unitary.two_normalizer_solvable (by omega) hm P hP hne
    let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective (inclusion_injective hN)
    let : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot _).mpr
      (fun hb => hne (bot_unique (hb ▸ hPB)))
    exact Group.IsPerfect.not_isSolvable B inferInstance
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    apply no_local_of_rank_le_one h
    rw [primeRank_equiv 3 e]
    let P : Sylow 3 (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := Classical.choice inferInstance
    exact P.primeRank_le_one_of_isCyclic
      (BenderSuzuki.MatrixGroups.suzukiSylow_isCyclic_of_ne_two (by omega) (by decide) P)

/-- Binary linear-three two-local normalizers have insufficient cubic rank. -/
theorem FourComponentLocalData.not_linear_three (h : FourComponentLocalData Q)
    {n : ℕ} (hn : 1 ≤ n) : ¬ ClassicalGroup.IsPSL Q 3 (2 ^ n) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  obtain ⟨B,P,hB,hr,hP,hne,hN,hPB,_⟩ := h.of_mulEquiv e
  let := hB
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  by_cases hn1 : n = 1
  · have hcard : Nat.card PSL(3,F) = 168 := by
      have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
      norm_num [hF,hn1,Fin.prod_univ_succ] at hc
      exact hc
    have hb : primeRank 3 PSL(3,F) ≤ 1 := by
      apply primeRank_le_one_of_square_not_dvd
      rw [hcard]; decide
    have := (primeRank_subgroup_le 3 B).trans hb
    omega
  obtain ⟨g,point,hg⟩ :=
    MainConverse.LinearThreeGeometry.twoLocal_conjugate_le F hn hF
      (normalizer (P : Set PSL(3,F))) ⟨P,hne,hP,rfl⟩
  let j := (MulAut.conj g).toMonoidHom.comp B.subtype
  have hj : j.range ≤ Matrix.PSL3.RootPlaneGeometry.parabolic F point := by
    rintro _ ⟨a,rfl⟩
    exact hg (mem_map_of_mem _ (hN a.property))
  apply Matrix.PSL3.LinearThree.PerfectSubgroups.no_perfect_odd_rank_two_in_parabolic
    F (by decide : Odd 3) hr (by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ n))
    j ((MulAut.conj g).injective.comp B.subtype_injective)
  cases point
  · exact Or.inr hj
  · exact Or.inl hj

/-- Binary symplectic four-dimensional two-local normalizers are excluded. -/
theorem FourComponentLocalData.not_symplectic (h : FourComponentLocalData Q)
    {n : ℕ} : ¬ ClassicalGroup.IsPSp Q 2 (2 ^ n) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨B,P,hB,hr,hP,hne,hN,hPB,_⟩ := h.of_mulEquiv
    (e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm)
  let := hB
  exact Theory.SpecificGroups.SymplecticFour.no_perfect_odd_rank_two_in_two_normalizer
    P hP hne (by decide : Odd 3) hr B.subtype B.subtype_injective
    (by simpa only [range_subtype] using hN)

/-- The genuine even G₂ model has the same perfect-normalizer obstruction. -/
theorem FourComponentLocalData.not_g2 (h : FourComponentLocalData Q)
    {n : ℕ} (hn : 2 ≤ n) : ¬ IsG2At Q (2 ^ n) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨B,P,hB,hr,hP,hne,hN,hPB,_⟩ := h.of_mulEquiv e
  let := hB
  have hb := Atlas.G2.PerfectSubgroups.perfect_subgroup_two_normalizer_odd_rank_le_one
    P hP hne (by
      rw [hF]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) hn)) B hN (by decide : Odd 3)
  omega

/-- Triality uses the actual fixed-point carrier and its actual parabolics. -/
theorem FourComponentLocalData.not_triality (h : FourComponentLocalData Q)
    {n : ℕ} (hn : 1 ≤ n) : ¬ Triality.Standard.IsTrialityGroupAt (2 ^ n) Q := by
  intro hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff Q n hn).mp hm
  obtain ⟨B,P,hB,hr,hP,hne,hN,hPB,_⟩ := h.of_mulEquiv e
  let := hB
  have hb := Triality.Standard.PerfectTwoNormalizer.perfect_subgroup_two_normalizer_odd_rank_le_one
    n hn P hP hne B hN (by decide : Odd 3)
  exact (by omega : ¬ primeRank 3 B ≤ 1) hb

/-- Full-form transport applies the two-local bound to every binary PSU₄ row. -/
theorem FourComponentLocalData.not_unitary_four (h : FourComponentLocalData Q)
    {n : ℕ} (hn : 1 ≤ n) : ¬ ClassicalGroup.IsPSU Q 4 (2 ^ n) := by
  rintro ⟨F,_,_,J,hF,hconj,⟨e⟩⟩
  let : CharP F 2 :=
    Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.charP_two n hn hF
  obtain ⟨a⟩ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
    J n hn hF hconj
  obtain ⟨B,P,hB,hr,hP,hne,hN,_,_⟩ := h.of_mulEquiv (e.trans a)
  let := hB
  have hb := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PerfectSubgroups.perfect_twoLocal_odd_primeRank_le_one
    J.conj J.conj_involutive n hn hF hconj (by decide : Odd 3)
    B.subtype B.subtype_injective (normalizer (P : Set _)) ⟨P,hne,hP,rfl⟩
    (by simpa only [range_subtype] using hN)
  omega

/-- The two actual PSU₅(4) parabolic orders are both lacking a factor seven. -/
theorem FourComponentLocalData.not_unitary_five (h : FourComponentLocalData Q) :
    ¬ ClassicalGroup.IsPSU Q 5 4 := by
  rintro ⟨F,_,_,J,hF,hconj,⟨e⟩⟩
  have hcard : Nat.card F = 16 := hF
  let : CharP F 2 := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hcard
  obtain ⟨a⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four J hcard hconj
  let J₀ := BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram.identityGram J
  obtain ⟨B,P,hB,hr,hP,hne,hN,_,h105⟩ := h.of_mulEquiv (e.trans a)
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Theory.SpecificGroups.UnitaryFive.finite_projective J₀
  obtain ⟨W,hw,hi,_,hNW⟩ :=
    Theory.SpecificGroups.UnitaryFive.IsotropicGeometry.projective_twoLocal_stabilizes_isotropic
      J₀ rfl (normalizer (P : Set _)) ⟨P,hne,hP,rfl⟩
  obtain ⟨b,g,hg⟩ := Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity.transitive
    J₀ hcard hconj rfl W hw hi
  have he : Theory.SpecificGroups.UnitaryFive.parabolic J₀ W =
      (if b then Theory.SpecificGroups.UnitaryFive.planeParabolic J₀
        else Theory.SpecificGroups.UnitaryFive.lineParabolic J₀).map
          (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J₀ g)).toMonoidHom := by
    rw [hg, Theory.SpecificGroups.UnitaryFive.IsotropicGeometry.parabolic_map_action]
    cases b <;> rfl
  have hd := h105.trans (card_dvd_of_le (hN.trans hNW))
  rw [he, card_map_of_injective (MulAut.conj _).injective] at hd
  cases b
  · change 105 ∣ Nat.card (Theory.SpecificGroups.UnitaryFive.lineParabolic J₀) at hd
    rw [Theory.SpecificGroups.UnitaryFive.card_lineParabolic_four J₀ hcard hconj rfl] at hd
    norm_num at hd
  · change 105 ∣ Nat.card (Theory.SpecificGroups.UnitaryFive.planeParabolic J₀) at hd
    rw [Theory.SpecificGroups.UnitaryFive.card_planeParabolic_four J₀ hcard hconj rfl] at hd
    norm_num at hd

open Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

/-- The Ree perfect-normalizer calculation applies to this literal residual. -/
theorem FourComponentLocalData.not_ree (h : FourComponentLocalData Q)
    {m : ℕ} (hm : 1 ≤ m) : ¬ Nonempty (Q ≃* ReeF4.Model m) := by
  rintro ⟨e⟩
  obtain ⟨B,P,hB,hr,hP,hne,hN,hPB,_⟩ := h.of_mulEquiv e
  let := hB
  have hb := ree_perfect_two_normalizer_odd_rank hm B P hP hne hN (by decide : Odd 3)
  omega

/-- The proved actual Tits embedding transfers the same local obstruction. -/
theorem FourComponentLocalData.not_tits (h : FourComponentLocalData Q) :
    ¬ Nonempty (Q ≃* Tits.ParrottGroup) := by
  rintro ⟨e⟩
  obtain ⟨B,P,hB,hr,hP,hne,hN,hPB,_⟩ := h.of_mulEquiv e
  let := hB
  have hb := tits_perfect_two_normalizer_odd_rank B P hP hne hN (by decide : Odd 3)
  omega

/-- All characteristic-two rank-two rows are excluded, retaining every
actual model equivalence and the fixed-field unitary convention. -/
theorem FourComponentLocalData.not_rank_two (h : FourComponentLocalData Q)
    (n : ℕ) : ¬ IsRankTwoModel Q n := by
  intro hm
  cases hm with
  | linear hn hm => exact h.not_linear_three hn hm
  | unitary_four hn hm => exact h.not_unitary_four hn hm
  | unitary_five hn hm =>
    exact h.not_unitary_five (by simpa only [hn, Nat.reducePow] using hm)
  | symplectic _ hm => exact h.not_symplectic hm
  | g2 hn hm => exact h.not_g2 hn hm
  | triality hn hm => exact h.not_triality hn hm
  | ree_f4 m hm _ he => exact h.not_ree hm he
  | tits _ he => exact h.not_tits he
  | symplectic_derived _ he =>
    obtain ⟨B,_,_,_,_,_,_,_,hd⟩ := h
    have hd' := hd.trans B.card_subgroup_dvd_card
    rw [Nat.card_congr (he.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
      nat_card_alternatingGroup] at hd'
    norm_num at hd'
  | g2_derived _ he =>
    obtain ⟨B,_,_,_,_,_,_,_,hd⟩ := h
    have hd' := hd.trans B.card_subgroup_dvd_card
    rw [Nat.card_congr he.some.toEquiv,
      Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd'
    norm_num at hd'

/-- The full B catalogue leaves two genuine central quotients. -/
theorem FourComponentLocalData.remaining_models (h : FourComponentLocalData Q)
    (hm : CFSG.Quasithin.ChapterA.Section02.IsTheoremBModel Q)
    (hr : 8 ≤ primeRank 2 Q) :
    ClassicalGroup.IsPSp Q 3 2 ∨ Nonempty (Q ≃* Janko4.Model) := by
  rcases hm.remaining_of_twoRank_ge_eight hr with ho | hb | ⟨f,hf⟩ | hs | hj
  · exact (CFSG.Quasithin.ChapterA.Section02.no_theoremB_odd_model_of_twoRank_ge_eight hr ho).elim
  · exact (h.not_bender hb).elim
  · exact (h.not_rank_two f hf).elim
  · exact Or.inl hs
  · exact Or.inr hj

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
