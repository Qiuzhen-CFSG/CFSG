module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.LateModels
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# Excluding the three exceptional terminal components

The full corrected B.5.1 conclusion on the late actor, together with the
actual later strong offender, gives `StrictRatioModel` for its relative
component. We compare all five surviving families with the actual exceptional
carriers. Their orders are 2520, 6048 and 1080, none divisible by 64.
The field-family order formulas therefore force SL₃ to be over the binary
prime field and exclude Sp₄ over a larger binary field. The remaining fixed
orders also differ.

Transport through `subgroupOfEquivOfLe` identifies this relative component
with the original `starImage H L`. In the triple-cover application the
carrier is precisely `HexEvenAutomorphisms`, as specified by
`HexSection.groupEquiv`. Thus the exclusions compare actual groups, including
possible accidental identifications between different classification rows.
They require no terminal point and retain the three universal earlier-source
inputs allowed by the contained-offender reduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the first
paragraph on printed p.1145 following (l) and (n) on p.1144; B.4.2, p.86,
and B.5.1, pp.99–103. The imported matrix and hexacode order calculations
retain their ATLAS source attribution and license in their owning modules.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.ExceptionalModels

open Subgroup Representation Representation.BinaryOffender
open ReducedModels ComponentReduction ModelReduction BinaryModels
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open scoped MatrixGroups IsMulCommutative

private theorem sl_card_mul (F : Type*) [Field F] [Finite F]
    (d : ℕ) [NeZero d] :
    Nat.card SL(d,F) * (Nat.card F - 1) =
      ∏ i : Fin d, (Nat.card F ^ d - Nat.card F ^ (i : ℕ)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(d,F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Atlas.ExceptionalSupport.card_psl_mul d

private theorem card_sl_three (F : BinaryField) :
    Nat.card SL(3,F.Carrier) =
      (2 ^ F.degree) ^ 3 * ((2 ^ F.degree) ^ 3 - 1) * ((2 ^ F.degree) ^ 2 - 1) := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center SL(3,F.Carrier))
  rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin] at hc
  exact (hc.trans (Matrix.PSL3.LinearThree.card_projective_mul_scalar F.Carrier)).trans
    (by rw [F.card_eq])

private theorem binary_exponent_le {N k : ℕ}
    (hc : N = 2520 ∨ N = 6048 ∨ N = 1080) (hd : 2 ^ k ∣ N) : k ≤ 5 := by
  by_contra hk
  have h64 : 64 ∣ N := (Nat.pow_dvd_pow 2 (show 6 ≤ k by omega)).trans hd
  rcases hc with rfl | rfl | rfl <;> norm_num at h64

/-- None of the actual strict-ratio component families has an exceptional
terminal order. The variable binary fields are included in the comparison. -/
theorem strict_model_card_ne_exceptional {D : Type*} [Group D]
    (h : StrictRatioModel D) {N : ℕ}
    (hN : N = 2520 ∨ N = 6048 ∨ N = 1080) : Nat.card D ≠ N := by
  intro hc
  unfold StrictRatioModel at h
  rcases h with ⟨F, ⟨e⟩⟩ | ⟨F, hn, ⟨e⟩⟩ | he | he | he
  · have he := (Nat.card_congr e.toEquiv).symm.trans hc
    have hd : 2 ^ (F.degree * 3) ∣ N := by
      rw [← he, card_sl_three, pow_mul]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    have hb := binary_exponent_le hN hd
    have hp := F.degree_pos
    have hn : F.degree = 1 := by omega
    rw [card_sl_three, hn] at he
    norm_num at he
    rcases hN with rfl | rfl | rfl <;> omega
  · have he := (Nat.card_congr e.toEquiv).symm.trans hc
    have hd : 2 ^ (F.degree * 4) ∣ N := by
      rw [← he, Theory.SpecificGroups.SymplecticFour.card_sp, F.card_eq, pow_mul]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    have hb := binary_exponent_le hN hd
    omega
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
    rcases hN with rfl | rfl | rfl <;> omega
  · obtain ⟨e⟩ := he
    have he := (Nat.card_congr e.toEquiv).symm.trans hc
    have ho := sl_card_mul (ZMod 2) 4
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
      Finset.prod_empty, mul_one] at ho
    rcases hN with rfl | rfl | rfl <;> omega
  · obtain ⟨e⟩ := he
    have he := (Nat.card_congr e.toEquiv).symm.trans hc
    have ho := sl_card_mul (ZMod 2) 5
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
      Finset.prod_empty, mul_one] at ho
    rcases hN with rfl | rfl | rfl <;> omega

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper)
    (s : StrongPlacement r)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ)

include s sections orbits source in
/-- Apply the strict model comparison to the original component, using its
proved containment in the late actor and the actual subgroup equivalence. -/
theorem component_card_ne_exceptional {N : ℕ}
    (hN : N = 2520 ∨ N = 6048 ∨ N = 1080) : Nat.card (starImage H L) ≠ N := by
  have hm := strict_late_component_model r s sections orbits source
  have hn := strict_model_card_ne_exceptional hm hN
  rw [Nat.card_congr
    (subgroupOfEquivOfLe (r.component_le_late_actor sections orbits)).toEquiv] at hn
  exact hn

include s sections orbits source in
/-- The strong placement excludes the A₇ branch of (l). -/
theorem not_seven : ¬ Nonempty (starImage H L ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  apply component_card_ne_exceptional r s sections orbits source (Or.inl rfl)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

include s sections orbits source in
/-- The strong placement excludes the actual derived binary G₂ carrier. -/
theorem not_g2 :
    ¬ Nonempty (starImage H L ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) := by
  rintro ⟨e⟩
  apply component_card_ne_exceptional r s sections orbits source (Or.inr (Or.inl rfl))
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
  exact Atlas.G2.BinaryException.card_H

include s sections orbits source in
/-- The literal even hexacode carrier excludes the triple-cover section
branch, independently of any point or projective-line stabilizer marking. -/
theorem not_hexSection :
    ¬ Nonempty (ModelSieve.HexSection r.placed.action.representation (starImage H L)) := by
  rintro ⟨h⟩
  apply component_card_ne_exceptional r s sections orbits source (Or.inr (Or.inr rfl))
  exact (Nat.card_congr h.groupEquiv.toEquiv).trans Atlas.Codes.hexEven_card

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.ExceptionalModels
