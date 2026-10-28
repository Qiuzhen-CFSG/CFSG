module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible

/-!
# The actual S3 stabilizer quotient closes the irreducible-component sieve

The marked S5 module supplies an S3 quotient of the original component
centralizer action. The ordinary source catalogue and the characteristic-two
star catalogue are excluded directly with that quotient: the rank-two outer
actions and the triality/Ree power actions cannot induce it. All quotient
maps and relative normalizers are those of the original selected vector.

This applies the existing model exclusions to the precise hypothesis they
consume. Earlier Control remains with the source assembly; no classification,
Sylow-reducibility or quaternion-action conclusion is assumed here.

Source: Aschbacher--Smith 13.1.12(3), printed pp.874--875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 Chapter1.XiEmbedding.InvariantLarge
open Chapter1.Section02.LocalModels SourceCentralizerStructure.Elimination
open ClassificationModels Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

private theorem alternating_action_excluded {A : Type*} [Group A] [Finite A]
    (h : HasOddSylowPair p A) (hp : 3 < p) (α : MulAut A)
    {n : ℕ} (hn : n = 6 ∨ n = 7) (σ : Equiv.Perm (Fin n))
    (ha : AlternatingAction α n σ) : False := by
  rcases ha with ⟨j,_⟩ | ⟨_,⟨jZ⟩,j,_⟩
  · exact h.not_alternating hp n (by omega) ⟨j⟩
  · apply h.not_of_card_dvd_orderBound hp
    rcases hn with rfl | rfl
    all_goals
      rw [card_eq_card_quotient_mul_card_subgroup (center A),
        Nat.card_congr j.toEquiv,Nat.card_congr jZ.toEquiv,nat_card_alternatingGroup]
      norm_num

/-- The source ordinary catalogue reduces to triality and Ree using only
the actual S3 stabilizer quotient on the original Frattini plane. -/
theorem ordinary_remaining_models_of_symmetricThree (h : Context T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hq : IsQuasisimple K)
    (hs : SymmetricThreeStabilizerQuotient L p u) :
    IsSimpleGroup K ∧ OrdinaryRemainingModels K := by
  let H := centralizer ({u} : Set G)
  let D := K.subgroupOf H
  let f : D ≃* K := subgroupOfEquivOfLe e.component.1
  let := hq
  let : IsQuasisimple D := hq.of_mulEquiv f.symm
  let q : XiQuotient K ≃* XiQuotient D :=
    QuotientGroup.congr _ _ f.symm (pCore_map_iso 2 f.symm)
  have hpair := h.component_oddSylowPair s e hi
  have hDpair := hpair.of_mulEquiv f.symm
  have hQpair := h.component_quotient_oddSylowPair s e hi
  have hQDpair := hQpair.of_mulEquiv q
  have hp := h.prime_gt_three
  obtain ⟨_,_,_,_,_,_,_,_,_,α,_,hm⟩ := h.ordinary_model_action c s e hq
  change ModelAction115 D α at hm
  cases hm with
  | lie hsimple hm _ =>
    let : IsSimpleGroup D := hsimple
    let : IsSimpleGroup K := f.symm.isSimpleGroup
    rcases hm with hm | hm | ⟨n,hn,hm⟩
    · exact (hDpair.not_bender hp (Group.IsPerfect.not_isMulCommutative D) hm).elim
    · cases hm with
      | linear n hn hm =>
        by_cases hn2 : 2 ≤ n
        · obtain ⟨F,_,_,hF,⟨j⟩⟩ := hm.of_mulEquiv f.symm
          let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
          exact (h.not_projective_linear_three s e hi F hn2 hF ⟨j⟩).elim
        · have hn1 : n = 1 := by omega
          subst n
          exact (hDpair.not_binary_linear hp 3 (Or.inl rfl) (by simpa using hm)).elim
      | symplectic n hn hm =>
        exact (h.not_ordinary_symplectic s e hi hq hs (by omega) (hm.of_mulEquiv f.symm)).elim
      | g2 n hn hm =>
        exact (h.not_ordinary_g2 s e hi hq hs (by omega) (hm.of_mulEquiv f.symm)).elim
      | triality n hn hm =>
        by_cases hn2 : 2 ≤ n
        · obtain ⟨P,hP,⟨j⟩⟩ := hm
          exact ⟨inferInstance,Or.inl ⟨n,hn2,P,hP,⟨f.symm.trans j⟩⟩⟩
        · have hn1 : n = 1 := by omega
          subst n
          exact (hDpair.not_triality_two hp (by simpa using hm)).elim
      | ree m hm he =>
        obtain ⟨d,⟨j⟩⟩ := he
        exact ⟨inferInstance,Or.inr ⟨m,hm,d,⟨f.symm.trans j⟩⟩⟩
      | symplectic_derived he => exact (hDpair.not_symplectic_derived hp he).elim
      | g2_derived he => exact (hDpair.not_g2_derived hp he).elim
      | tits he => exact (hDpair.not_tits hp he.some).elim
    · exact (hDpair.not_binary_linear hp n (Or.inr hn) hm).elim
  | two_cover _ _ hm _ =>
    rcases hm with hm | hm
    · exact (hQDpair.not_linear_three_four hp hm).elim
    · exact (h.not_ordinary_g2_quotient s e hi hq hs (n := 2) (by decide)
        (hm.of_mulEquiv q)).elim
  | six σ _ ha => exact (alternating_action_excluded hDpair hp α (Or.inl rfl) σ ha).elim
  | seven σ _ ha => exact (alternating_action_excluded hDpair hp α (Or.inr rfl) σ ha).elim
  | odd hm _ =>
    rcases hm with hm | ⟨r,hr,hm⟩
    · exact (hDpair.not_linear_three_three hp hm).elim
    · exact (hDpair.not_prime_linear_two h.odd hr.1 hm).elim
  | sporadic name hn hm _ =>
    let : IsSimpleGroup (XiQuotient K) := e.ordinary_quotient_simple hq
    let : IsSimpleGroup (XiQuotient D) := q.symm.isSimpleGroup
    let : Group.IsPerfect (XiQuotient D) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 D))
    exact (hQDpair.not_sporadic hp name hn hm).elim


/-- The S3 quotient excludes the whole ordinary irreducible branch, using
the source catalogue and its actual Sylow actions. -/
theorem not_ordinary_of_symmetricThree (h : Context T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hq : IsQuasisimple K)
    (hs : SymmetricThreeStabilizerQuotient L p u) : False := by
  obtain ⟨hK,hm⟩ := ordinary_remaining_models_of_symmetricThree h c s e hi hq hs
  let := hK
  rcases hm with ⟨n,hn,hm⟩ | ⟨m,hm,he⟩
  · exact h.not_ordinary_triality s e hi hs hn hm
  · exact h.not_ordinary_ree s e hi hq hs hm he

/-- The same actual S3 quotient excludes both surviving characteristic-two
star families, with their source center and kernel bounds. -/
theorem not_characteristic_two_of_symmetricThree (h : Context T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hf : generalizedFitting K = pCore 2 K)
    (hs : SymmetricThreeStabilizerQuotient L p u) : False := by
  rcases h.characteristic_two_rankTwo_models c s hnt e hi hf with ⟨F,hn,⟨j⟩⟩ | ⟨F,hn,⟨j⟩⟩
  · exact h.not_symplectic_star c s hnt e hi hf hs F hn j
  · exact h.not_g2_star c s hnt e hi hf hs F hn j

/-- The source centralizer sieve consumes the S3 quotient directly.
Every model branch is discharged under the original relative action. -/
theorem not_escape_of_irreducible_symmetricThree (h : Context T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hs : SymmetricThreeStabilizerQuotient L p u) : False := by
  rcases e.ordinary_or_characteristic_two with hq | hf
  · exact not_ordinary_of_symmetricThree h c s e hi hq hs
  · exact not_characteristic_two_of_symmetricThree h c s hnt e hi hf hs

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
