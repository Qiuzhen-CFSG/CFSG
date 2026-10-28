module

public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Descent
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.Quotient

/-!
# Transfer of the odd triality centralizer calculation

The elementary centralizer maps onto the centralizer in the actual central
quotient when the elementary center has prime-to-p order. A normal complementary
SL₂ image of prime-to-p index therefore contains the residual after quotienting.
Together with the p-element inclusion from `Descent`, this yields the marked
residual equivalence. The argument uses no perfectness assumption and includes
SL₂(3).

Two geometric inputs remain explicit: the split commutation/scalar identities
and relative normality with prime-to-p index in the elementary centralizer.
The permitted quotient faithfulness of the complementary map discharges the
coprime-center premise from the same index calculation. This module does not assert
these inputs or the unconditional source centralizer theorem.

Sources: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith A.2.17, printed p.39, especially (*) and the final triality case.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups

namespace Triality.Standard.OddFundamentalCentralizer
open Parabolics

variable {P : Parameters} (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)

/-- The elementary center embeds in the quotient of the elementary centralizer
by the complementary image. Quotient faithfulness of the complement eliminates
the intersection, so the index calculation also proves coprimality of the center. -/
theorem coprime_center_of_elementary_index
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hnormal : (elementaryCentralizerHom D C hcomm).range.Normal)
    (hindex : Nat.Coprime P.prime (elementaryCentralizerHom D C hcomm).range.index)
    (hj : Function.Injective (complementHom D C)) :
    Nat.Coprime P.prime (Nat.card (Subgroup.center (ElementaryGroup P))) := by
  let N := (elementaryCentralizerHom D C hcomm).range
  let : N.Normal := hnormal
  have hle : Subgroup.center (ElementaryGroup P) ≤ elementaryCentralizer D :=
    Subgroup.center_le_centralizer ((fundamentalLift D).range : Set (ElementaryGroup P))
  let i := Subgroup.inclusion hle
  let f := (QuotientGroup.mk' N).comp i
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro z hz
    have hzN : i z ∈ N := (QuotientGroup.eq_one_iff (N := N) (i z)).mp hz
    obtain ⟨a, ha⟩ := hzN
    have hae : complementLift D C a = z.val := congrArg Subtype.val ha
    have haq : complementHom D C a = 1 :=
      (toCarrier_complementLift D C a).symm.trans
        ((congrArg (toCarrier P) hae).trans ((toCarrier_eq_one P z.val).mpr z.property))
    have ha1 : a = 1 := hj (haq.trans (map_one (complementHom D C)).symm)
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact hae.symm.trans ((congrArg (complementLift D C) ha1).trans (map_one _))
  have hcard : Nat.card (Subgroup.center (ElementaryGroup P)) ∣ N.index :=
    Subgroup.card_dvd_of_injective f hf
  exact hindex.coprime_dvd_right hcard

/-- Relative normality and prime-to-p index before the actual central quotient
imply the required reverse containment in its literal centralizer residual. -/
theorem residual_mem_complement_range_of_coprime_center
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hcenter : Nat.Coprime P.prime (Nat.card (Subgroup.center (ElementaryGroup P))))
    (hnormal : (elementaryCentralizerHom D C hcomm).range.Normal)
    (hindex : Nat.Coprime P.prime (elementaryCentralizerHom D C hcomm).range.index)
    (x : residual P) : x.val.val ∈ (complementHom D C).range := by
  let N := (elementaryCentralizerHom D C hcomm).range
  have hsurj := centralizerQuotient_surjective D hcenter
  let : (N.map (centralizerQuotient D)).Normal := hnormal.map _ hsurj
  have hcoprime : Nat.Coprime P.prime (N.map (centralizerQuotient D)).index :=
    hindex.coprime_dvd_right (N.index_map_dvd hsurj)
  have hx : x.val ∈ N.map (centralizerQuotient D) :=
    Subgroup.primeToResidual_le _ hcoprime x.property
  obtain ⟨y, ⟨a, rfl⟩, ha⟩ := hx
  refine ⟨a, ?_⟩
  exact (centralizerQuotient_elementaryCentralizerHom D C hcomm a).symm.trans
    (congrArg Subtype.val ha)

/-- Quotient faithfulness discharges the central-kernel premise from the same
relative normality and index calculation; no independent center bound is needed. -/
theorem residual_mem_complement_range_of_elementary_index
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hnormal : (elementaryCentralizerHom D C hcomm).range.Normal)
    (hindex : Nat.Coprime P.prime (elementaryCentralizerHom D C hcomm).range.index)
    (hj : Function.Injective (complementHom D C)) (x : residual P) :
    x.val.val ∈ (complementHom D C).range :=
  residual_mem_complement_range_of_coprime_center D C hcomm
    (coprime_center_of_elementary_index D C hcomm hnormal hindex hj) hnormal hindex x

/-- Assemble the marked residual equivalence from the elementary matrix index
calculation. The underlying ambient map is exactly `complementHom D C`. -/
def residualEquivOfElementaryIndex
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hnormal : (elementaryCentralizerHom D C hcomm).range.Normal)
    (hindex : Nat.Coprime P.prime (elementaryCentralizerHom D C hcomm).range.index)
    (hj : Function.Injective (complementHom D C)) :
    SL(2, ExtensionField P) ≃* residual P :=
  residualEquiv D (complementHom D C)
    (fundamentalHom_complementHom_commute_of_split D C hcomm) hj
    (residual_mem_complement_range_of_elementary_index D C hcomm hnormal hindex hj)

@[simp] theorem residualEquivOfElementaryIndex_apply_val
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hnormal : (elementaryCentralizerHom D C hcomm).range.Normal)
    (hindex : Nat.Coprime P.prime (elementaryCentralizerHom D C hcomm).range.index)
    (hj : Function.Injective (complementHom D C)) (a : SL(2, ExtensionField P)) :
    (residualEquivOfElementaryIndex D C hcomm hnormal hindex hj a).val.val =
      complementHom D C a := rfl

/-- The split scalar calculation gives the exact common scalar intersection,
with the original fundamental subgroup and quotient maps. -/
theorem mem_fundamental_inf_complement_iff_of_split
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hneg : D.centralFixedEmbedding (-1) = splitComplementHom D C (-1))
    (hk : Function.Injective (fundamentalHom D)) (x : Carrier P) :
    x ∈ fundamental P ⊓ (complementHom D C).range ↔
      x = 1 ∨ x = fundamentalHom D (-1) :=
  mem_fundamental_inf_range_iff D (complementHom D C)
    (fundamentalHom_complementHom_commute_of_split D C hcomm) hk
    (fundamentalHom_neg_one_eq_complementHom_of_split D C hneg) x

/-- The source's defining-characteristic rank lower bound needs only the split
commutation calculation and quotient faithfulness, independently of exhaustion. -/
theorem three_mul_exponent_le_residual_rank_of_split
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hj : Function.Injective (complementHom D C)) :
    3 * P.exponent ≤ primeRank P.prime (residual P) :=
  three_mul_exponent_le_residual_rank D (complementHom D C)
    (fundamentalHom_complementHom_commute_of_split D C hcomm) hj

end Triality.Standard.OddFundamentalCentralizer
