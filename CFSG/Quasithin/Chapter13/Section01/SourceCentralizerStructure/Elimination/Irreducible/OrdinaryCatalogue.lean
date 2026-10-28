module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.OrdinaryRankTwo
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddSylowPairs.Finite
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddSylowPairs.PrimeLinearTwo

/-!
# The ordinary marked catalogue reduced to triality and Ree

The original 1.1.5 action catalogue is applied to the actual component in
C_G(u). Its odd-complement Sylow pair excludes every rank-one, alternating,
sporadic, binary-linear and small derived row. The genuine stabilizer S₃
section excludes Sp₄ and G₂, with the ordinary center bound discharging all
quotient-kernel premises. The linear-three whole model is excluded by the
already proved actual Sylow/unipotent argument. Two-central covers retain
their own quotient maps; their PSL₃(4) and G₂(4) quotients are also excluded.

Only nonbinary triality and Ree remain. Their construction and exclusion,
and final irreducible assembly, remain with qt-d-1317-centralizer-irreducible.
This is a source-derived reduction, not the full source contradiction.
SieveActions retains its existing producer qt-d-1317-module-orbits.

Source: Aschbacher–Smith, 1.1.5(3), pp.501–503; 13.1.12(3), pp.874–875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding.InvariantLarge Chapter1.Section02.LocalModels
open ClassificationModels Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The two uneliminated families, on the whole ordinary component. -/
@[expose] def OrdinaryRemainingModels (K : Type*) [Group K] : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2^n) K) ∨
    (∃ m : ℕ, 1 ≤ m ∧ IsReeF4At K m)

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

/-- Every ordinary escape has a genuine nonbinary triality or Ree whole model.
All other marked 1.1.5 alternatives are discharged from the source hypotheses. -/
theorem Context.ordinary_remaining_simple_models (h : Context T L p)
    (a : SieveActions h) (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hq : IsQuasisimple K) :
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
  have hs := (h.sylow_reducible_and_symmetric_three a c s hnt e hi).2
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

/-- The original catalogue interface, with simplicity retained separately by
`ordinary_remaining_simple_models` for the actual remaining-row consumers. -/
theorem Context.ordinary_remaining_models (h : Context T L p)
    (a : SieveActions h) (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hq : IsQuasisimple K) :
    OrdinaryRemainingModels K :=
  (h.ordinary_remaining_simple_models a c s hnt e hi hq).2

/-- Literal centralizer application of the narrowed ordinary catalogue.
The remaining triality/Ree exclusion stays with this task's final assembly. -/
theorem Context.centralizer_le_of_ordinary_remaining_exclusion (h : Context T L p)
    (o : OrbitFacts T L p) (a : SieveActions h) (c : Control T L p)
    (hremaining : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        IsQuasisimple K → OrdinaryRemainingModels K → False)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
  apply h.centralizer_le_of_ordinary_irreducible_exclusion o a c _ hred hu hne
  intro v s hnt K e hi hq
  exact hremaining v s hnt K e hi hq (h.ordinary_remaining_models a c s hnt e hi hq)

/-- The actual TI consumer with all non-triality/Ree ordinary rows discharged. -/
theorem Context.ti_of_ordinary_remaining_exclusion (h : Context T L p)
    (o : OrbitFacts T L p) (a : SieveActions h) (c : Control T L p)
    (hremaining : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        IsQuasisimple K → OrdinaryRemainingModels K → False)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) := by
  apply h.ti_of_ordinary_irreducible_exclusion o a c _ hred
  intro v s hnt K e hi hq
  exact hremaining v s hnt K e hi hq (h.ordinary_remaining_models a c s hnt e hi hq)

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
