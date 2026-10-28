module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.ComponentLocals
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PerfectSubgroups
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport
public import Theory.SpecificGroups.ClassicalUnitary.FivePerfectLocals
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.PerfectCore
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ReeTits

/-!
# Excluding every placed characteristic-two model

The original residual's perfect image in K/Z(K) has cubic rank at least
two, normalizes a nontrivial two-subgroup, and retains a factor of 31 in
its order. The actual rank-one and rank-two parabolic calculations exclude
all Bender, linear, symplectic, G₂, triality, Ree and Tits models. Full
Hermitian-form transport supplies the unitary-four bound; both actual
PSU₅(4) parabolic orders are prime to 31. The two small derived models
are likewise excluded by their certified orders.

Consequently the previously placed catalogue leaves only the actual J₄
central quotient. This is the characteristic-two step of the source,
not either of its separate J₄ endgames. The original Hall counterexample
consumer in OddNormalizer discharges the local configuration hypotheses.
Source: Aschbacher--Smith 4.4.12, printed pp.621--622. The Ree and Tits
local bounds are reused from the proved Chapter 11 model extension; no
unfinished source assertion from that task is used.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
open ClassificationModels
variable {Q : Type*} [Group Q] [Finite Q]

private theorem no_local_of_rank_le_one (h : ExteriorComponentLocalData Q)
    (hr : primeRank 3 Q ≤ 1) : False := by
  obtain ⟨B,_,_,hb,_,_,_⟩ := h
  have := (primeRank_subgroup_le 3 B).trans hr
  omega

/-- Every Bender row is incompatible with the actual placed residual. -/
theorem ExteriorComponentLocalData.not_bender (h : ExteriorComponentLocalData Q) :
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
theorem ExteriorComponentLocalData.not_linear_three (h : ExteriorComponentLocalData Q)
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
theorem ExteriorComponentLocalData.not_symplectic (h : ExteriorComponentLocalData Q)
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
theorem ExteriorComponentLocalData.not_g2 (h : ExteriorComponentLocalData Q)
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
theorem ExteriorComponentLocalData.not_triality (h : ExteriorComponentLocalData Q)
    {n : ℕ} (hn : 1 ≤ n) : ¬ Triality.Standard.IsTrialityGroupAt (2 ^ n) Q := by
  intro hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff Q n hn).mp hm
  obtain ⟨B,P,hB,hr,hP,hne,hN,hPB,_⟩ := h.of_mulEquiv e
  let := hB
  have hb := Triality.Standard.PerfectTwoNormalizer.perfect_subgroup_two_normalizer_odd_rank_le_one
    n hn P hP hne B hN (by decide : Odd 3)
  exact (by omega : ¬ primeRank 3 B ≤ 1) hb

/-- Full-form transport applies the two-local bound to every binary PSU₄ row. -/
theorem ExteriorComponentLocalData.not_unitary_four (h : ExteriorComponentLocalData Q)
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

/-- The two actual PSU₅(4) parabolic orders are both prime to 31. -/
theorem ExteriorComponentLocalData.not_unitary_five (h : ExteriorComponentLocalData Q) :
    ¬ ClassicalGroup.IsPSU Q 5 4 := by
  rintro ⟨F,_,_,J,hF,hconj,⟨e⟩⟩
  have hcard : Nat.card F = 16 := hF
  let : CharP F 2 := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hcard
  obtain ⟨a⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four J hcard hconj
  let J₀ := BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram.identityGram J
  obtain ⟨B,P,hB,hr,hP,hne,hN,_,h31⟩ := h.of_mulEquiv (e.trans a)
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
  have hd := h31.trans (card_dvd_of_le (hN.trans hNW))
  rw [he, card_map_of_injective (MulAut.conj _).injective] at hd
  cases b
  · change 31 ∣ Nat.card (Theory.SpecificGroups.UnitaryFive.lineParabolic J₀) at hd
    rw [Theory.SpecificGroups.UnitaryFive.card_lineParabolic_four J₀ hcard hconj rfl] at hd
    norm_num at hd
  · change 31 ∣ Nat.card (Theory.SpecificGroups.UnitaryFive.planeParabolic J₀) at hd
    rw [Theory.SpecificGroups.UnitaryFive.card_planeParabolic_four J₀ hcard hconj rfl] at hd
    norm_num at hd

open Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

/-- The Ree perfect-normalizer calculation applies to this literal residual. -/
theorem ExteriorComponentLocalData.not_ree (h : ExteriorComponentLocalData Q)
    {m : ℕ} (hm : 1 ≤ m) : ¬ Nonempty (Q ≃* ReeF4.Model m) := by
  rintro ⟨e⟩
  obtain ⟨B,P,hB,hr,hP,hne,hN,hPB,_⟩ := h.of_mulEquiv e
  let := hB
  have hb := ree_perfect_two_normalizer_odd_rank hm B P hP hne hN (by decide : Odd 3)
  omega

/-- The proved actual Tits embedding transfers the same local obstruction. -/
theorem ExteriorComponentLocalData.not_tits (h : ExteriorComponentLocalData Q) :
    ¬ Nonempty (Q ≃* Tits.ParrottGroup) := by
  rintro ⟨e⟩
  obtain ⟨B,P,hB,hr,hP,hne,hN,hPB,_⟩ := h.of_mulEquiv e
  let := hB
  have hb := tits_perfect_two_normalizer_odd_rank B P hP hne hN (by decide : Odd 3)
  omega

/-- All characteristic-two rank-two rows are excluded, retaining every
actual model equivalence and the fixed-field unitary convention. -/
theorem ExteriorComponentLocalData.not_rank_two (h : ExteriorComponentLocalData Q)
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

/-- Only the actual J₄ carrier remains among the previously placed models. -/
theorem ExteriorComponentLocalData.jankoFour_of_placed_models
    (h : ExteriorComponentLocalData Q) (hm : ExteriorPlacedComponentModels Q) :
    Nonempty (Q ≃* Janko4.Model) := by
  rcases hm with hb | ⟨n,hn⟩ | hj
  · exact (h.not_bender hb).elim
  · exact (h.not_rank_two n hn).elim
  · exact hj

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
