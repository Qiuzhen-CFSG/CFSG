module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSInputs
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Context
public import CFSG.Quasithin.ChapterC.Section04.A5LinearThreeComplete
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
public import Theory.NumberTheory.BinaryTorusParity

/-!
# The full linear-three quotient in the original A₅ source configuration

The original A₅ span excludes a star component over the field of two elements.
For even field degree the star component has center of order three. The
quasisimple source quotient has center of order at most three, so its
surjection onto the star component is injective on the center and hence
injective everywhere. For odd degree the ordinary central-cover theorem
makes the source center trivial. Both arguments retain the literal star
map, including at field four, without assuming that the component is a block.

Thus an actual SL₃ star row supplies the full quotient marking required by
`msPair_of_quotient`. Selection of that row and the whole-core MS alternatives
remain separate source duties.

Source: Aschbacher–Smith A.3.6, pp.43–45, C.2.7, pp.145–147, and the
full-quotient step in original 4.3.8, p.616.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC ChapterC.C27Source ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

private theorem injective_of_center_card_le
    {Q D : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    [Group D] [Finite D] [Nontrivial D]
    (f : Q →* D) (hf : Function.Surjective f)
    (hk : f.ker ≤ center Q)
    (hc : Nat.card (center Q) ≤ Nat.card (center D)) : Function.Injective f := by
  have he : (center D).comap f = center Q :=
    IsQuasisimple.comap_center_of_surjective f hf
  let j : center Q →* center D := (f.comp (center Q).subtype).codRestrict _
    (fun x => he.ge x.property)
  have hj : Function.Surjective j := by
    intro y
    obtain ⟨x,hx⟩ := hf y.val
    have hxz : x ∈ center Q := he.le (by change f x ∈ center D; rw [hx]; exact y.property)
    exact ⟨⟨x,hxz⟩,Subtype.ext hx⟩
  have hji : Function.Injective j := (hj.bijective_of_nat_card_le hc).1
  apply f.ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  have heq : (⟨x,hk hx⟩ : center Q) = 1 := hji (by
    apply Subtype.ext
    change f x = f 1
    simpa only [map_one] using (MonoidHom.mem_ker.mp hx))
  exact congrArg Subtype.val heq

/-- The original A₅ span excludes the binary SL₃ star row. -/
theorem linearThree_degree_gt_one_of_a5
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (F : BinaryField)
    (e : starImage (K c) (c.I.pCoreIn 2) (K c) ≃* SL(3,F.Carrier)) :
    1 < F.degree := by
  by_contra hn
  have hd : F.degree = 1 := by have hp := F.degree_pos; omega
  apply c.c28.no_a5_component_of_central_fiveFree d.quotient c.K c.component c.quotient
    c.block_source_outside
  rw [Nat.card_congr (c.c28.constrained_linear_three_simple_equiv c.K c.component
    c.quotient c.block_source_outside hf e).toEquiv,
    Matrix.PSL3.LinearThree.card_projective F.Carrier,F.card_eq,hd]
  norm_num

/-- The actual comparison from the full two-core quotient loses no central
kernel in the original A₅ linear-three row, including the field-four case. -/
theorem linearThree_coreToStar_injective_of_a5
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (F : BinaryField)
    (e : starImage (K c) (c.I.pCoreIn 2) (K c) ≃* SL(3,F.Carrier)) :
    Function.Injective (coreToStar c.block_radical_normalizes) := by
  let h := c.block_source_input hf
  let Q := K c ⧸ pCore 2 (K c)
  let : IsQuasisimple Q := h.quasisimple
  let : Nontrivial SL(3,F.Carrier) := (Matrix.PSL3.projection_surjective F.Carrier).nontrivial
  let f : Q →* SL(3,F.Carrier) := e.toMonoidHom.comp (coreToStar h.normalizes)
  have hfs : Function.Surjective f := e.surjective.comp (coreToStar_surjective h.normalizes)
  have hker : f.ker ≤ center Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact coreToStar_ker_central_from_source h
  have hn := linearThree_degree_gt_one_of_a5 d c hf F e
  have hfi : Function.Injective f := by
    rcases Nat.even_or_odd F.degree with heven | hodd
    · apply injective_of_center_card_le f hfs hker
      have hd : 3 ∣ 2 ^ F.degree - 1 :=
        (Nat.BinaryTorusParity.three_dvd_sub_one_iff F.degree).mpr heven
      have hz : Nat.card (center SL(3,F.Carrier)) = 3 := by
        rw [Atlas.ExceptionalSupport.card_sl_center,Fintype.card_fin,F.card_eq,
          Nat.gcd_eq_left_iff_dvd.mpr hd]
      rw [hz]
      change Nat.card (center (K c ⧸ pCore 2 (K c))) ≤ 3
      have hc : Nat.card (center (K c ⧸ pCore 2 (K c))) = 1 ∨
          Nat.card (center (K c ⧸ pCore 2 (K c))) = 3 :=
        coreQuotient_center_card_from_source h
      rcases hc with hc | hc <;> omega
    · have hn3 : 3 ≤ F.degree := by have := Nat.odd_iff.mp hodd; omega
      have h8 : 8 ≤ Nat.card F.Carrier := by
        rw [F.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn3
      have hd := Matrix.PSL3.OrdinaryCenterRecognition.center_card_dvd
        (by omega : Nat.card F.Carrier ≠ 2) (by omega : Nat.card F.Carrier ≠ 4)
        (Section04Constrained.source_linear_three_equiv h e)
      rw [F.card_eq,(Nat.BinaryTorusParity.coprime_three_sub_one hodd).gcd_eq_one] at hd
      have hz : center Q = ⊥ := (center Q).eq_bot_of_card_eq (Nat.dvd_one.mp hd)
      exact f.ker_eq_bot_iff.mp (bot_unique (hker.trans hz.le))
  intro x y hxy
  exact hfi (congrArg e hxy)

/-- The full original quotient, with the same SL₃ star marking. -/
@[expose] noncomputable def linearThree_fullQuotientEquiv_of_a5
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (F : BinaryField)
    (e : starImage (K c) (c.I.pCoreIn 2) (K c) ≃* SL(3,F.Carrier)) :
    (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier) :=
  (MulEquiv.ofBijective (coreToStar c.block_radical_normalizes)
    ⟨linearThree_coreToStar_injective_of_a5 d c hf F e,
      coreToStar_surjective c.block_radical_normalizes⟩).trans e

/-- The full-quotient recognition retains the original projection triangle. -/
@[simp] theorem linearThree_fullQuotientEquiv_of_a5_mk
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (F : BinaryField)
    (e : starImage (K c) (c.I.pCoreIn 2) (K c) ≃* SL(3,F.Carrier)) (k : K c) :
    linearThree_fullQuotientEquiv_of_a5 d c hf F e (QuotientGroup.mk' (pCore 2 (K c)) k) =
      e (toStarImage (K c) (c.I.pCoreIn 2) k) := rfl

/-- The same original star row supplies every MS-pair hypothesis on the
literal component and radical, with no full-quotient premise left over. -/
theorem linearThree_msPair_of_a5_star
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (F : BinaryField)
    (e : starImage (K c) (c.I.pCoreIn 2) (K c) ≃* SL(3,F.Carrier)) :
    FullSieve.SourceInterface.LinearThreeMSPair KnownSimple.IsKnownSimple
      (K c) (c.I.pCoreIn 2) F.degree F.Carrier :=
  msPair_of_quotient c d.chosen hf F.degree
    (le_of_lt (linearThree_degree_gt_one_of_a5 d c hf F e)) F.card_eq
    (linearThree_fullQuotientEquiv_of_a5 d c hf F e)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
