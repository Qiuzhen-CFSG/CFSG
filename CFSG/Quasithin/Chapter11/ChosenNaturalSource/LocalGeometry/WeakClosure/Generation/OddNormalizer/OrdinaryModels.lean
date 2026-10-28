module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.QuotientOrder
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceA5Normality

/-!
# Ordinary components of the nonbinary covering residual

The literal residual retains an odd prime of rank at least two. Its
projection through an ordinary component has only a two-group kernel.
The actual binary linear-three, symplectic, G₂ and triality normalizer
bounds contradict this rank; full quotient orders exclude binary degrees
four and five. The general C.3 exclusions handle rank one and odd
characteristic. The complete Theorem C list then leaves only actual Ree,
Tits and sporadic central-quotient models.

ModelReduction applies these exclusions to the original pushing-up pair.
The remaining exceptional rows are still obligations of this task.
Source: Aschbacher--Smith C.3.1--5, pp.149--151, and 4.4.6, p.620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
variable {H M B R W : Subgroup G}
include D S

theorem ordinary_natural_span_rank
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 ≤ primeRank p (conjugateSpanBy B M) := by
  obtain ⟨p,hp,ho,hr⟩ := exists_odd_rank_two D S
  let : Fact p.Prime := ⟨hp⟩
  have hb : 2 ≤ primeRank p B := by
    rw [←primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 B) pCore_isPGroup,
      primeRank_congr p e]
    exact hr
  exact ⟨p,hp,ho,hb.trans (Theory.GroupTheory.primeRank_le_of_injective p
    (inclusion (le_conjugateSpanBy B M)) (inclusion_injective _))⟩

theorem no_ordinary_natural_small
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K)
    (hc : Nat.card (K ⧸ center K) < 60480) : False := by
  have hd := ordinary_natural_quotient_card_dvd h e K hK
  have hl := Nat.le_of_dvd (Nat.card_pos (α := K ⧸ center K)) hd
  have hb := quotient_card_ge D S
  omega

theorem no_ordinary_natural_linear_binary
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) n 2) : False := by
  obtain ⟨F,_,_,hF,⟨ek⟩⟩ := hm
  rcases hn with rfl | rfl
  · apply no_ordinary_natural_small D S h e K hK
    rw [Nat.card_congr ek.toEquiv]
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    norm_num [hF,Fin.prod_univ_succ] at hc
    rw [hc]; decide
  · have hd := ordinary_natural_quotient_card_dvd h e K hK
    rw [Nat.card_congr ek.toEquiv] at hd
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    norm_num [hF,Fin.prod_univ_succ] at hc
    rw [hc] at hd
    exact quotient_order_not_dvd_binary_five D S hd

theorem no_ordinary_natural_linear_three
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K)
    {n : ℕ} (hn : 1 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n)) : False := by
  obtain ⟨F,_,_,hF,⟨ek⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  by_cases hn1 : n = 1
  · apply no_ordinary_natural_small D S h e K hK
    rw [Nat.card_congr ek.toEquiv]
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    norm_num [hF,hn1,Fin.prod_univ_succ] at hc
    rw [hc]; decide
  obtain ⟨p,hp,ho,hr⟩ := ordinary_natural_span_rank D S (M := M) e
  let : Fact p.Prime := ⟨hp⟩
  have hbound : primeRank p (conjugateSpanBy B M) ≤ 1 := by
    apply h.ordinary_span_primeRank_le_of_model_two_normalizers K hK ek ho
    intro X P hX hP hne hnP
    let := hX
    by_contra! hb
    obtain ⟨g,point,hg⟩ :=
      MainConverse.LinearThreeGeometry.twoLocal_conjugate_le F hn hF
        (normalizer (P : Set PSL(3,F))) ⟨P,hne,hP,rfl⟩
    let j := (MulAut.conj g).toMonoidHom.comp X.subtype
    have hj : j.range ≤ Matrix.PSL3.RootPlaneGeometry.parabolic F point := by
      refine le_trans ?_ hg
      rintro _ ⟨a,rfl⟩
      exact mem_map_of_mem _ (hnP a.property)
    apply Matrix.PSL3.LinearThree.PerfectSubgroups.no_perfect_odd_rank_two_in_parabolic
      F ho (by omega) (by
        rw [hF]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ n))
      j ((MulAut.conj g).injective.comp X.subtype_injective)
    cases point
    · exact Or.inr hj
    · exact Or.inl hj
  omega

theorem no_ordinary_natural_symplectic
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K) {n : ℕ}
    (hm : ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ n)) : False := by
  obtain ⟨F,_,_,hF,⟨ek⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨p,hp,ho,hr⟩ := ordinary_natural_span_rank D S (M := M) e
  let : Fact p.Prime := ⟨hp⟩
  have hb := h.ordinary_span_primeRank_le_one_of_sp4 K hK
    (ek.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm) ho
  omega

theorem no_ordinary_natural_g2
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassificationModels.IsG2At (K ⧸ center K) (2 ^ n)) : False := by
  obtain ⟨F,_,_,hF,⟨ek⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨p,hp,ho,hr⟩ := ordinary_natural_span_rank D S (M := M) e
  let : Fact p.Prime := ⟨hp⟩
  have hb := h.ordinary_span_primeRank_le_one_of_g2 K hK ek
    (by
      rw [hF]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) hn)) ho
  omega

theorem no_ordinary_natural_triality
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K) {n : ℕ} (hn : 1 ≤ n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (K ⧸ center K)) : False := by
  obtain ⟨p,hp,ho,hr⟩ := ordinary_natural_span_rank D S (M := M) e
  let : Fact p.Prime := ⟨hp⟩
  have hb := h.ordinary_span_primeRank_le_one_of_isTrialityGroupAt K hK hn hm ho
  omega

/-- The remaining catalogue contains actual central-quotient identifications. -/
@[expose] def OrdinaryRemainder (Q : Type*) [Group Q] : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ Nonempty (Q ≃* ReeF4.Model m)) ∨
  Nonempty (Q ≃* Tits.ParrottGroup) ∨
  (∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
    Nonempty (Q ≃* name.Carrier))

theorem ordinary_natural_models
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K) : OrdinaryRemainder (K ⧸ center K) := by
  let := hK.2
  have hm := Chapter1.QuasisimpleInvolutions.quotient_model (h.sqtk.subgroup K)
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple
  have small := no_ordinary_natural_small D S h e K hK
  cases hm with
  | alternating n hn ek =>
    apply (small ?_).elim
    rw [Nat.card_congr ek.some.toEquiv]
    have hb := (alternatingGroup (Fin n)).card_le_card_group
    rw [Nat.card_perm, Nat.card_fin] at hb
    exact lt_of_le_of_lt (hb.trans (Nat.factorial_le hn)) (by decide)
  | odd hm => exact (h.no_ordinary_component_of_theoremC_odd_model K hK hm).elim
  | bender hm =>
    cases hm with
    | linear f hf hm =>
      obtain ⟨F,_,_,hF,⟨ek⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact (h.no_ordinary_component_sl2_central_quotient K hK
        (ek.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)).elim
    | unitary f hf hm => exact (h.no_ordinary_component_binary_unitary_three K hK hf hm).elim
    | suzuki m hm ek => exact (h.no_ordinary_component_suzuki_central_quotient K hK hm ek.some).elim
  | rank_two f hm =>
    cases hm with
    | linear hf hm => exact (no_ordinary_natural_linear_three D S h e K hK hf hm).elim
    | symplectic hf hm => exact (no_ordinary_natural_symplectic D S h e K hK hm).elim
    | g2 hf hm => exact (no_ordinary_natural_g2 D S h e K hK hf hm).elim
    | triality hf hm => exact (no_ordinary_natural_triality D S h e K hK hf hm).elim
    | ree_f4 m hm hf ek => exact Or.inl ⟨m,hm,ek⟩
    | symplectic_derived hf ek =>
      apply (small ?_).elim
      rw [Nat.card_congr (ek.some.trans
        Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
        nat_card_alternatingGroup]
      norm_num
    | g2_derived hf ek =>
      apply (small ?_).elim
      rw [Nat.card_congr ek.some.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
      decide
    | tits hf ek => exact Or.inr (Or.inl ek)
  | linear_binary n hn hm => exact (no_ordinary_natural_linear_binary D S h e K hK hn hm).elim
  | sporadic hm =>
    rcases hm with ⟨n,hn,ek⟩ | ⟨ek⟩
    · exact Or.inr (Or.inr ⟨n,hn,ek⟩)
    · exact (h.no_ordinary_component_janko_central_quotient K hK ek.some).elim
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
