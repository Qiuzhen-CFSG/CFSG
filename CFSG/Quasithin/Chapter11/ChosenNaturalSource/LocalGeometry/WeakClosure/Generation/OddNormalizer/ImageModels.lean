module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.CoverImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ReeTits
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.SmallSylow
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.PerfectCore
public import Theory.SpecificGroups.Janko1.Model.Certification.Order

/-!
# Excluding the shared C-models for the placed natural residual

The actual central image is perfect, has nontrivial two-core, and normalizes
the elementary image of the original V. Rank-one normalizers and the binary
rank-two local bounds rule out all characteristic-two Lie families. The
retained module forces two-rank at least six, excluding the odd C-models.
The full module and actor orders force twelve factors of two, leaving only
J₄ and Ru among the finite rows. No quotient cover is replaced by its
projective quotient.

The source endpoint applies this inspection in the literal N_G(A), after
proved residual placement. Source: Aschbacher--Smith 4.4.12 and the following
model inspection, printed pp.621--622.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {Q : Type*} [Group Q] [Finite Q]
include D S

omit S [Finite G] [Finite Q] in
theorem NaturalCoverImage.product_card_dvd (h : NaturalCoverImage D Q) :
    Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) ∣ Nat.card Q := by
  obtain ⟨X,U,hX,hU,hUX,hN,hcard,⟨a⟩⟩ := h
  have hc : Nat.card D.chosenCentralQuotient ∣ Nat.card (pCore 2 X) := by
    have hd := hcard.trans (card_dvd_of_le hUX)
    rwa [pCoreIn,card_map_of_injective X.subtype_injective] at hd
  have hx : Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) ∣ Nat.card X := by
    rw [← Nat.card_congr a.toEquiv,card_eq_card_quotient_mul_card_subgroup (pCore 2 X),mul_comm]
    exact Nat.mul_dvd_mul (dvd_refl _) hc
  exact hx.trans X.card_subgroup_dvd_card

omit [Finite Q] in
theorem NaturalCoverImage.two_power_dvd (h : NaturalCoverImage D Q) : 2 ^ 12 ∣ Nat.card Q := by
  obtain ⟨hv,hq⟩ := natural_two_parts D S
  have hd : 2 ^ 12 ∣ Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) := by
    simpa only [show (64 * 64 : ℕ) = 2 ^ 12 by decide] using Nat.mul_dvd_mul hv hq
  exact hd.trans (h.product_card_dvd D)

private theorem no_small_image (h : NaturalCoverImage D Q)
    (hc : Nat.card Q < 60480) : False := by
  have hd : Nat.card (L ⧸ pCore 2 L) ∣ Nat.card Q :=
    (dvd_mul_left _ _).trans (h.product_card_dvd D)
  have hb := Nat.le_of_dvd (Nat.card_pos (α := Q)) hd
  have hl := quotient_card_ge D S
  omega

private theorem no_image_of_perfect_core_trivial (h : NaturalCoverImage D Q)
    (hc : ∀ X : Subgroup Q, Group.IsPerfect X → pCore 2 X = ⊥) : False := by
  obtain ⟨X,U,hX,hU,hUX,hne,hN,hsize,hr⟩ := h.local_data D S
  have he := hc X hX
  rw [pCoreIn,he,Subgroup.map_bot] at hUX
  exact hne (bot_unique hUX)

private theorem no_image_of_local_odd_rank (h : NaturalCoverImage D Q)
    (hc : ∀ (X U : Subgroup Q), Group.IsPerfect X → IsPGroup 2 U → U ≠ ⊥ →
      X ≤ normalizer (U : Set Q) →
      ∀ p : ℕ, p.Prime → Odd p → primeRank p X ≤ 1) : False := by
  obtain ⟨X,U,hX,hU,hUX,hne,hN,hsize,p,hp,ho,hr⟩ := h.local_data D S
  have hb := hc X U hX hU.isPGroup hne hN p hp ho
  omega

private theorem no_bender_image (h : NaturalCoverImage D Q)
    (hm : ClassificationModels.IsBenderModel Q) : False := by
  cases hm with
  | linear f hf hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    apply no_image_of_perfect_core_trivial D S
      (h.of_equiv D (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm))
    intro X hX
    let := hX
    exact Matrix.SpecialLinearGroup.perfect_subgroup_twoCore_eq_bot X
  | unitary f hf hm =>
    apply no_image_of_perfect_core_trivial D S h
    intro X hX
    let := hX
    exact ChapterF.Source.Unitary.perfect_subgroup_twoCore_eq_bot (by omega) hm X
  | suzuki m hm e =>
    apply no_image_of_perfect_core_trivial D S (h.of_equiv D e.some)
    intro X hX
    let := hX
    by_contra hn
    let : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot _).mpr (by
      intro he
      have : Subsingleton X := by rw [he]; infer_instance
      exact hn (Subsingleton.elim _ _))
    let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
    exact Group.IsPerfect.not_isSolvable X
      (BenderSuzuki.MatrixGroups.suzukiSubgroup_isSolvable_of_solvable_normal hm X (pCore 2 X) hn)

private theorem no_linear_three_image (h : NaturalCoverImage D Q)
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSL Q 3 (2 ^ n)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hi := h.of_equiv D e
  by_cases hn1 : n = 1
  · apply no_small_image D S hi
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    norm_num [hF,hn1,Fin.prod_univ_succ] at hc
    rw [hc]; decide
  apply no_image_of_local_odd_rank D S hi
  intro X U hX hU hne hN p hp ho
  let := hX
  let : Fact p.Prime := ⟨hp⟩
  by_contra! hb
  obtain ⟨g,point,hg⟩ := MainConverse.LinearThreeGeometry.twoLocal_conjugate_le F hn hF
    (normalizer (U : Set PSL(3,F))) ⟨U,hne,hU,rfl⟩
  let j := (MulAut.conj g).toMonoidHom.comp X.subtype
  have hj : j.range ≤ Matrix.PSL3.RootPlaneGeometry.parabolic F point := by
    refine le_trans ?_ hg
    rintro _ ⟨a,rfl⟩
    exact mem_map_of_mem _ (hN a.property)
  apply Matrix.PSL3.LinearThree.PerfectSubgroups.no_perfect_odd_rank_two_in_parabolic
    F ho (by omega) (by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ n))
    j ((MulAut.conj g).injective.comp X.subtype_injective)
  cases point
  · exact Or.inr hj
  · exact Or.inl hj

private theorem no_rank_two_image (h : NaturalCoverImage D Q)
    {f : ℕ} (hm : ChapterA.Section02.IsTheoremCRankTwoModel Q f) : False := by
  cases hm with
  | linear hf hm => exact no_linear_three_image D S h hf hm
  | symplectic hf hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    apply no_image_of_local_odd_rank D S (h.of_equiv D
      (e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm))
    intro X U hX hU hne hN p hp ho
    let := hX
    let : Fact p.Prime := ⟨hp⟩
    by_contra! hb
    apply Theory.SpecificGroups.SymplecticFour.no_perfect_odd_rank_two_in_two_normalizer
      U hU hne ho (by omega) X.subtype X.subtype_injective
    simpa only [range_subtype] using hN
  | g2 hf hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    apply no_image_of_local_odd_rank D S (h.of_equiv D e)
    intro X U hX hU hne hN p hp ho
    let := hX
    let : Fact p.Prime := ⟨hp⟩
    exact Atlas.G2.PerfectSubgroups.perfect_subgroup_two_normalizer_odd_rank_le_one
      U hU hne (by
        rw [hF]
        exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hf)) X hN ho
  | triality hf hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff Q f hf).mp hm
    apply no_image_of_local_odd_rank D S (h.of_equiv D e)
    intro X U hX hU hne hN p hp ho
    let := hX
    let : Fact p.Prime := ⟨hp⟩
    exact Triality.Standard.PerfectTwoNormalizer.perfect_subgroup_two_normalizer_odd_rank_le_one
      f hf U hU hne X hN ho
  | ree_f4 m hm hf e =>
    apply no_image_of_local_odd_rank D S (h.of_equiv D e.some)
    intro X U hX hU hne hN p hp ho
    let := hX
    let : Fact p.Prime := ⟨hp⟩
    exact ree_perfect_two_normalizer_odd_rank hm X U hU hne hN ho
  | symplectic_derived hf e =>
    apply no_small_image D S (h.of_equiv D
      (e.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix))
    rw [nat_card_alternatingGroup]; norm_num
  | g2_derived hf e =>
    apply no_small_image D S (h.of_equiv D e.some)
    rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]; decide
  | tits hf e =>
    apply no_image_of_local_odd_rank D S (h.of_equiv D e.some)
    intro X U hX hU hne hN p hp ho
    let := hX
    let : Fact p.Prime := ⟨hp⟩
    exact tits_perfect_two_normalizer_odd_rank X U hU hne hN ho

omit D S in
private theorem held_not_two_power : ¬ 2 ^ 12 ∣ Nat.card Held.He := by
  obtain ⟨P,hP⟩ := Held.LocalPairs.SylowGeometry.Calculations.exists_representative_sylow
    Held.LocalPairs.SylowGeometry.Calculations.representative_isPGroup
    Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.normalizer_eq
  intro hd
  have hdP := P.pow_dvd_card_of_pow_dvd_card hd
  have hc : Nat.card P ≤ 1024 := by
    rw [hP]
    exact (Nat.card_le_card_of_surjective _
      Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.normalForm_surjective).trans
      (by simp)
  have hp := Nat.le_of_dvd (Nat.card_pos (α := P)) hdP
  norm_num at hp
  omega

/-- Every shared C-model containing the actual natural covering image is
J₄ or Ru. All rank-one, rank-two, odd-characteristic and other finite rows
are excluded on the literal full quotient and its nontrivial module image. -/
theorem NaturalCoverImage.theoremC_models (h : NaturalCoverImage D Q)
    (hm : ChapterA.Section02.IsTheoremCModel Q) :
    Nonempty (Q ≃* Janko4.Model) ∨ Nonempty (Q ≃* Rudvalis.Model) := by
  have hd := h.two_power_dvd D S
  cases hm with
  | alternating n hn e =>
    apply (no_small_image D S h ?_).elim
    rw [Nat.card_congr e.some.toEquiv]
    have hb := (alternatingGroup (Fin n)).card_le_card_group
    rw [Nat.card_perm,Nat.card_fin] at hb
    exact lt_of_le_of_lt (hb.trans (Nat.factorial_le hn)) (by decide)
  | odd hm =>
    have hl := h.twoRank_ge_six D S
    have hu := hm.twoRank_le_two
    omega
  | bender hm => exact (no_bender_image D S h hm).elim
  | rank_two f hm => exact (no_rank_two_image D S h hm).elim
  | linear_binary n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv] at hd
    rcases hn with rfl | rfl
    · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
      norm_num [hF,Fin.prod_univ_succ] at hc
      rw [hc] at hd
      norm_num at hd
    · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
      norm_num [hF,Fin.prod_univ_succ] at hc
      rw [hc] at hd
      norm_num at hd
  | sporadic hm =>
    rcases hm with ⟨n,hn,⟨e⟩⟩ | ⟨e⟩
    · rw [Nat.card_congr e.toEquiv] at hd
      cases n with
      | m11 => change 2 ^ 12 ∣ Nat.card Sporadic.Mathieu.M11 at hd; rw [Sporadic.Mathieu.m11_order] at hd; norm_num at hd
      | m12 => change 2 ^ 12 ∣ Nat.card Sporadic.Mathieu.M12 at hd; rw [Sporadic.Mathieu.m12_order] at hd; norm_num at hd
      | m22 => change 2 ^ 12 ∣ Nat.card Sporadic.Mathieu.M22 at hd; rw [Sporadic.Mathieu.m22_order] at hd; norm_num at hd
      | m23 => change 2 ^ 12 ∣ Nat.card Sporadic.Mathieu.M23 at hd; rw [Sporadic.Mathieu.m23_order] at hd; norm_num at hd
      | m24 => change 2 ^ 12 ∣ Nat.card Sporadic.Mathieu.M24 at hd; rw [Sporadic.Mathieu.m24_order] at hd; norm_num at hd
      | j2 =>
        change 2 ^ 12 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier at hd
        rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
        norm_num at hd
      | j3 => exact (hn rfl).elim
      | hs =>
        have hh := hd.trans Sporadic.LeechRelated.HS.card_carrier_dvd
        norm_num at hh
      | he => exact (held_not_two_power hd).elim
      | j4 => exact Or.inl ⟨e⟩
      | ru => exact Or.inr ⟨e⟩
    · rw [Nat.card_congr e.some.toEquiv,Janko1.card_model] at hd
      norm_num at hd
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
