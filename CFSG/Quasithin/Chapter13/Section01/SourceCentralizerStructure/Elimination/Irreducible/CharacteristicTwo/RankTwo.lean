module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.CharacteristicTwo
public import Theory.SpecificGroups.SL2.BinaryOddRank

/-!
# The remaining characteristic-two source models

The canonical odd complement embeds in K/O₂(K), and the genuine C.2.7
central-kernel bound embeds it further in K*. Its noncyclicity excludes
SL₂; its order contains p², excluding every small exceptional star model.
For an SL₃ star model, the actual central comparison identifies
(K/O₂(K))/Z(K/O₂(K)) with PSL₃. The previously proved quotient-action
obstruction eliminates that row without reconstructing a whole SL₃ cover
or assuming a parabolic marking.

Only the large symplectic and G₂ star families remain. The centralizer and
TI applications state those two exclusions and the ordinary branch explicitly;
their construction and final irreducible assembly remain with this task,
qt-d-1317-centralizer-irreducible. This is a source-derived reduction, not a
proof of the full escaping-component contradiction. Earlier Control and
OrbitFacts retain qt-d-1317-centralizer-sieve and qt-d-1317-module-orbits as
producers, respectively.

Source: Aschbacher–Smith, 13.1.12(3), pp.874–875; C.2.7, pp.145–147.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding
open Chapter1.RadicalExclusions.ModelReduction FullSieve
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

private theorem Context.star_odd_complement (h : Context T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hf : generalizedFitting K = pCore 2 K) :
    ∃ B : Subgroup (starImage K (centralizerCore T L p u) K), XiOddQuotient p B := by
  let input := h.characteristic_two_input c s hnt e hi hf
  let X := XiP p L
  let P : Sylow p X := Sylow.nonempty.some
  let P₀ := (P : Subgroup X).map X.subtype
  have hPX : P₀ ≤ X := map_subtype_le _
  have hP : XiOddQuotient p P₀ :=
    (RadicalConjugateRigidity.maximal_radical_structure
      h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides).1.of_mulEquiv
      (RadicalActions.ambientSylowQuotientEquiv h.odd
        (RadicalConjugateRigidity.maximal_radical_structure
          h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides).1.isPGroup P).symm
  have hPK : P₀ ≤ K := hPX.trans (h.radical_le_component s e hi)
  let j := InvariantLarge.componentMap hPK
  have hj : Function.Injective j := InvariantLarge.componentMap_injective hP.isPGroup h.odd hPK
  let f := coreToStar input.normalizes
  have hz : Nat.Coprime p (Nat.card (center (XiQuotient K))) := by
    rcases coreQuotient_center_card_from_source input with hc | hc
    · rw [hc]; exact Nat.coprime_one_right p
    · rw [hc]
      exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (by decide) h.prime_gt_three)
  have hk : Nat.Coprime p (Nat.card f.ker) :=
    hz.of_dvd_right (card_dvd_of_le (coreToStar_ker_central_from_source input))
  have hfj := injective_comp_subtype_of_coprime_ker f hk j.range
    (hP.isPGroup.of_surjective j.rangeRestrict j.rangeRestrict_surjective)
  have hcomp : Function.Injective (f.comp j) := by
    intro a b hab
    apply hj
    exact congrArg Subtype.val (hfj (a₁ := j.rangeRestrict a) (a₂ := j.rangeRestrict b) hab)
  let g := f.comp j
  let z : P₀ ≃* g.range := MulEquiv.ofBijective g.rangeRestrict
    ⟨fun a b hab => hcomp (congrArg Subtype.val hab),g.rangeRestrict_surjective⟩
  exact ⟨g.range,hP.of_mulEquiv z⟩

private theorem not_prime_square_orderBound (hp : p.Prime) (hl : 3 < p) :
    ¬ p^2 ∣ 2^10 * 3^3 * 5 * 7 * 31 := by
  intro hd
  have hd' : p ∣ 2^10 * 3^3 * 5 * 7 * 31 := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hd
  simp only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : 10 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31)] at hd'
  have he : p=5 ∨ p=7 ∨ p=31 := by omega
  rcases he with rfl | rfl | rfl <;> norm_num at hd

private theorem not_small_star {A : Type*} [Group A] [Finite A]
    (hp : 3 < p) (B : Subgroup A) (hB : XiOddQuotient p B)
    (hc : Nat.card A ∣ 2^10 * 3^3 * 5 * 7 * 31) : False := by
  have hd : p^2 ∣ Nat.card B := by
    rcases hB with ⟨_,hc⟩ | ⟨_,hc,_⟩
    · rw [hc]
    · rw [hc]; exact pow_dvd_pow p (by decide : 2 ≤ 3)
  exact not_prime_square_orderBound (Fact.out : p.Prime) hp
    (hd.trans ((card_subgroup_dvd_card B).trans hc))

private def centerCongruence {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private theorem star_remaining {A : Type*} [Group A] [Finite A]
    (hp : 3 < p) (hm : StarModels.Model A) (B : Subgroup A) (hB : XiOddQuotient p B) :
    (∃ F : BinaryField, 2 ≤ F.degree ∧ Nonempty (A ≃* SL(3,F.Carrier))) ∨
    (∃ F : BinaryField, 1 < F.degree ∧ Nonempty (A ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)) ∨
    (∃ F : BinaryField, 1 < F.degree ∧ Nonempty (A ≃* Atlas.G2.Model F.Carrier)) := by
  cases hm with
  | linearTwo F e =>
    exact (hB.not_isCyclic (Matrix.SL2.odd_pGroup_isCyclic_of_injective hB.isPGroup
      (by omega) (e.toMonoidHom.comp B.subtype) (e.injective.comp B.subtype_injective))).elim
  | linearThree F e =>
    by_cases hn : 2 ≤ F.degree
    · exact Or.inl ⟨F,hn,⟨e⟩⟩
    have hn1 : F.degree = 1 := by have := F.degree_pos; omega
    have hcard : Nat.card F.Carrier = 2 := by rw [F.card_eq,hn1]; rfl
    exfalso
    apply not_small_star hp B hB
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F.Carrier) 3
    rw [hcard] at hc
    norm_num [Fin.prod_univ_succ] at hc
    have hc' : Nat.card PSL(3,F.Carrier) = 168 := by
      simpa only [Nat.card_eq_fintype_card] using hc
    have ha := card_eq_card_quotient_mul_card_subgroup (center A)
    rw [Nat.card_congr (centerCongruence e).toEquiv,hc',
      Nat.card_congr (centerCongr e).toEquiv,Atlas.ExceptionalSupport.card_sl_center,hcard] at ha
    norm_num at ha
    rw [ha]; norm_num
  | symplectic F hn e => exact Or.inr (Or.inl ⟨F,hn,⟨e⟩⟩)
  | g2 F hn e => exact Or.inr (Or.inr ⟨F,hn,⟨e⟩⟩)
  | g2DerivedTwo e =>
    exfalso
    apply not_small_star hp B hB
    rw [Nat.card_congr e.toEquiv,Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      Atlas.G2.BinaryException.card_H]
    norm_num
  | alternating n hn e =>
    exfalso
    apply not_small_star hp B hB
    rw [Nat.card_congr e.toEquiv]
    rcases hn with rfl | rfl | rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num
  | linearFiveTwo e =>
    exfalso
    apply not_small_star hp B hB
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
    norm_num [Fin.prod_univ_succ] at hc
    have hc' : Nat.card PSL(5,ZMod 2) = 9999360 := by
      simpa only [Nat.card_eq_fintype_card] using hc
    have ha := card_eq_card_quotient_mul_card_subgroup (center A)
    rw [Nat.card_congr (centerCongruence e).toEquiv,hc',
      Nat.card_congr (centerCongr e).toEquiv,Atlas.ExceptionalSupport.card_sl_center] at ha
    norm_num at ha
    rw [ha]; norm_num
  | tripleSix ec eq =>
    exfalso
    apply not_small_star hp B hB
    rw [card_eq_card_quotient_mul_card_subgroup (center A),
      Nat.card_congr eq.toEquiv,Nat.card_congr ec.toEquiv,nat_card_alternatingGroup]
    norm_num


/-- The actual C.2.7 catalogue leaves only the large symplectic and G₂ rows.
The complement and every excluded row are constructed from the source data;
no linear-three model list or parabolic marking is assumed. -/
theorem Context.characteristic_two_rankTwo_models (h : Context T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hf : generalizedFitting K = pCore 2 K) :
    (∃ F : BinaryField, 1 < F.degree ∧
      Nonempty (starImage K (centralizerCore T L p u) K ≃*
        Matrix.symplecticGroup (Fin 2) F.Carrier)) ∨
    (∃ F : BinaryField, 1 < F.degree ∧
      Nonempty (starImage K (centralizerCore T L p u) K ≃* Atlas.G2.Model F.Carrier)) := by
  obtain ⟨B,hB⟩ := h.star_odd_complement c s hnt e hi hf
  rcases star_remaining h.prime_gt_three
      (h.characteristic_two_star_model c s hnt e hi hf) B hB with hm | hm
  · obtain ⟨F,hn,⟨j⟩⟩ := hm
    let input := h.characteristic_two_input c s hnt e hi hf
    have hb := (kernel_offender_from_source input).1.upper
    let eQ := coreStarCenterEquiv input.normalizes input.quasisimple
      (starImage_ne_bot_of_bound input.normalizes input.quasisimple hb)
    let eF : (XiQuotient K ⧸ center (XiQuotient K)) ≃* PSL(3,F.Carrier) :=
      eQ.trans (centerCongruence j)
    have hz : Nat.Coprime p (Nat.card (center (XiQuotient K))) := by
      rcases coreQuotient_center_card_from_source input with hc | hc
      · rw [hc]; exact Nat.coprime_one_right p
      · rw [hc]
        exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
          (Nat.not_dvd_of_pos_of_lt (by decide) h.prime_gt_three)
    have hq := (RadicalConjugateRigidity.maximal_radical_structure
      h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides).1
    obtain ⟨S,_,hSX⟩ := h.component_sylow e
    exact (core_quotient_linearThree_excluded F.Carrier hn F.card_eq h.odd (XiP p L)
      (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) K
      (h.radical_le_local s) (XiP_invariant p inf_le_left)
      (h.local_normalizes_component s e hi) (h.radical_le_component s e hi)
      hq hi.local hz eF S hSX).elim
  · exact hm

/-- Literal centralizer application of the constructed characteristic-two sieve.
The ordinary branch, the two remaining star families and the reducible
component-normalizer branch remain explicit mathematical obligations. -/
theorem Context.centralizer_le_of_rankTwo_exclusions (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p)
    (hordinary : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        IsQuasisimple K → False)
    (hsymplectic : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        generalizedFitting K = pCore 2 K →
        ∀ F : BinaryField, 1 < F.degree →
          Nonempty (starImage K (centralizerCore T L p u) K ≃*
            Matrix.symplecticGroup (Fin 2) F.Carrier) → False)
    (hg2 : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        generalizedFitting K = pCore 2 K →
        ∀ F : BinaryField, 1 < F.degree →
          Nonempty (starImage K (centralizerCore T L p u) K ≃* Atlas.G2.Model F.Carrier) → False)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
  apply h.centralizer_le_of_component_exclusions o c _ hred hu hne
  intro v s hnt K e hi
  rcases e.ordinary_or_characteristic_two with hq | hf
  · exact hordinary v s hnt K e hi hq
  · rcases h.characteristic_two_rankTwo_models c s hnt e hi hf with
        ⟨F,hn,hm⟩ | ⟨F,hn,hm⟩
    · exact hsymplectic v s hnt K e hi hf F hn hm
    · exact hg2 v s hnt K e hi hf F hn hm

/-- TI follows from these same literal remaining branches. Their discharge,
and the final irreducible contradiction, remain with this source owner. -/
theorem Context.ti_of_rankTwo_exclusions (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p)
    (hordinary : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        IsQuasisimple K → False)
    (hsymplectic : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        generalizedFitting K = pCore 2 K →
        ∀ F : BinaryField, 1 < F.degree →
          Nonempty (starImage K (centralizerCore T L p u) K ≃*
            Matrix.symplecticGroup (Fin 2) F.Carrier) → False)
    (hg2 : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        generalizedFitting K = pCore 2 K →
        ∀ F : BinaryField, 1 < F.degree →
          Nonempty (starImage K (centralizerCore T L p u) K ≃* Atlas.G2.Model F.Carrier) → False)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) := by
  apply h.ti_of_component_exclusions o c _ hred
  intro v s hnt K e hi
  rcases e.ordinary_or_characteristic_two with hq | hf
  · exact hordinary v s hnt K e hi hq
  · rcases h.characteristic_two_rankTwo_models c s hnt e hi hf with
        ⟨F,hn,hm⟩ | ⟨F,hn,hm⟩
    · exact hsymplectic v s hnt K e hi hf F hn hm
    · exact hg2 v s hnt K e hi hf F hn hm

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
