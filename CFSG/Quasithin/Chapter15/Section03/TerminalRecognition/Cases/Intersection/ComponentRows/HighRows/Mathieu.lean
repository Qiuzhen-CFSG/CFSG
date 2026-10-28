module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Basic
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Actions
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Permutation
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.Mathieu.M12.Properties.Simplicity

/-!
# The Mathieu rows in the terminal component comparison

The checked order of M₁₂ differs from every component order in B.5.6(1).
For the field families, monotonicity places 95040 strictly between two
successive values of the order polynomial. The triple cover has order
1080 from its literal center and quotient. These comparisons apply to the
actual offender F*, identified with the ambient F* by `offender_fitting_eq`.
They exclude F.6.18(12) and (13) in either ordering of the local factors.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.1/B.5.6, printed pp.99–105, F.6.18, pp.309–310,
and the final proof of 15.3.1, p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace ComponentRows.HighRows

private theorem sl_card_mul (F : Type*) [Field F] [Finite F]
    (n : ℕ) [NeZero n] :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) F) * (Nat.card F - 1) =
      ∏ i : Fin n, (Nat.card F ^ n - Nat.card F ^ (i : ℕ)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin n) F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Atlas.ExceptionalSupport.card_psl_mul n

private theorem sl_three_card (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h := sl_card_mul F 3
  change Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) * (q - 1) = _ at h
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one] at h
  have h1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    ring
  have h2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega)
  rw [h, h1, h2]
  ring

private theorem sl_two_order_ne (q : ℕ) : q * (q ^ 2 - 1) ≠ 95040 := by
  intro h
  by_cases hq : q ≤ 45
  · have hh : q * (q ^ 2 - 1) ≤ 45 * (45 ^ 2 - 1) := by gcongr
    omega
  · have hh : 46 * (46 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by gcongr <;> omega
    omega

private theorem sl_three_order_ne (q : ℕ) :
    q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) ≠ 95040 := by
  intro h
  by_cases hq : q ≤ 4
  · have hh : q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) ≤
        4 ^ 3 * (4 ^ 3 - 1) * (4 ^ 2 - 1) := by gcongr
    omega
  · have hh : 5 ^ 3 * (5 ^ 3 - 1) * (5 ^ 2 - 1) ≤
        q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) := by gcongr <;> omega
    omega

private theorem sp_order_ne (q : ℕ) :
    q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1) ≠ 95040 := by
  intro h
  by_cases hq : q ≤ 3
  · have hh : q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1) ≤
        3 ^ 4 * (3 ^ 2 - 1) * (3 ^ 4 - 1) := by gcongr
    omega
  · have hh : 4 ^ 4 * (4 ^ 2 - 1) * (4 ^ 4 - 1) ≤
        q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1) := by gcongr <;> omega
    omega

private theorem g2_order_ne (q : ℕ) :
    q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) ≠ 95040 := by
  intro h
  by_cases hq : q ≤ 2
  · have hh : q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) ≤
        2 ^ 6 * (2 ^ 6 - 1) * (2 ^ 2 - 1) := by gcongr
    omega
  · have hh : 3 ^ 6 * (3 ^ 6 - 1) * (3 ^ 2 - 1) ≤
        q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := by gcongr <;> omega
    omega

/-- The actual M₁₂ marking is incompatible with every component model in B.5.6. -/
theorem not_mathieuTwelve_model {L : Type*} [Group L]
    (e : L ≃* Sporadic.Mathieu.M12) : ¬ QuasisimpleModel L := by
  have hc : Nat.card L = 95040 := (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m12_order
  intro h
  cases h with
  | linearTwo F f =>
    rw [Nat.card_congr f.toEquiv, Atlas.card_sl_two] at hc
    exact sl_two_order_ne _ hc
  | linearThree F f =>
    rw [Nat.card_congr f.toEquiv, sl_three_card] at hc
    exact sl_three_order_ne _ hc
  | symplecticFour F f =>
    rw [Nat.card_congr f.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp] at hc
    exact sp_order_ne _ hc
  | g2 F f =>
    rw [Nat.card_congr f.toEquiv, Atlas.G2.card_Model] at hc
    exact g2_order_ne _ hc
  | alternatingSix f =>
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup] at hc
    norm_num at hc
  | alternatingSeven f =>
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup] at hc
    norm_num at hc
  | tripleSix a b =>
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
    rw [Nat.card_congr a.toEquiv, Nat.card_congr b.toEquiv, nat_card_alternatingGroup,
      hc] at hh
    norm_num at hh
  | g2DerivedTwo f =>
    rw [Nat.card_congr f.toEquiv, Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      Atlas.G2.BinaryException.card_H] at hc
    norm_num at hc
  | linearFourTwo f =>
    have hh := sl_card_mul (ZMod 2) 4
    rw [← Nat.card_congr f.toEquiv, hc] at hh
    norm_num [Fin.prod_univ_succ] at hh
  | linearFiveTwo f =>
    have hh := sl_card_mul (ZMod 2) 5
    rw [← Nat.card_congr f.toEquiv, hc] at hh
    norm_num [Fin.prod_univ_succ] at hh

end ComponentRows.HighRows

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)
include d

/-- F.6.18(13) is impossible: its actual component is M₁₂, whereas the
full source action gives one of the ten incompatible B.5.6 components.
The proof also applies to either labeling of its local subgroups. -/
theorem component_row_thirteen_false
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (e : generalizedFitting (coreQuotient H) ≃* Sporadic.Mathieu.M12) : False := by
  let f : generalizedFitting d.offenderGroup ≃* generalizedFitting (coreQuotient H) :=
    (MulEquiv.subgroupCongr (d.offender_fitting_eq hL)).trans
      (subgroupOfEquivOfLe ((d.fitting_le_thompson hL).trans d.thompson_image_le_offender))
  exact ComponentRows.HighRows.not_mathieuTwelve_model (f.trans e)
    (c.fittingModel d.offenderAction)

/-- F.6.18(12) is impossible in either local labeling. Simplicity of the
already constructed M₁₂ model identifies the ambient F* before comparison. -/
theorem component_row_twelve_false
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (e : coreQuotient H ≃* Sporadic.Mathieu.M12) : False := by
  let _ := Sporadic.Mathieu.m12_isSimpleGroup
  let _ : IsSimpleGroup (coreQuotient H) := e.isSimpleGroup
  have ht : generalizedFitting (coreQuotient H) = ⊤ := by
    have hn : generalizedFitting (coreQuotient H) ≠ ⊥ := by
      let _ := hL.simple
      let _ : Nontrivial (generalizedFitting (coreQuotient H)) :=
        (QuotientGroup.mk'_surjective (center (generalizedFitting (coreQuotient H)))).nontrivial
      exact (nontrivial_iff_ne_bot _).mp inferInstance
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_left hn
  exact d.component_row_thirteen_false hL c
    ((MulEquiv.subgroupCongr ht).trans (topEquiv.trans e))

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
