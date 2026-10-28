module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SourceComponentRows.Actions

/-!
# Odd-field rows for the corrected source action

Cyclic Sylow three-subgroups supply the rank-one bound where it is
needed. Field orders and the existing exceptional isomorphisms then
exclude rows (4),(5), and give SL₃(2), A₆, or S₆ in rows (6),(8).
Both local labelings retain the original source input.

The proofs adapt the existing terminal `ComponentRows` comparison to the
full `ProjectiveLine.QuasisimpleSourceConclusion`. The two-dimensional
F₄ offender clause remains on the original action; no legacy clause is
constructed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1/B.5.6,
printed pp.99–105; F.6.18, pp.309–310; K.1.3, p.453; final proof of
15.3.1, p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

private noncomputable def source_ambientFittingEquivOffender
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H))) :
    generalizedFitting (coreQuotient H) ≃* generalizedFitting d.offenderGroup :=
  (subgroupOfEquivOfLe
    ((d.fitting_le_thompson hL).trans d.thompson_image_le_offender)).symm.trans
    (MulEquiv.subgroupCongr (d.offender_fitting_eq hL).symm)

private theorem source_odd_psl_component_models
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (F : FSource.FieldParameter) (ho : Odd F.prime) (hp3 : F.prime ≠ 3)
    (hseven : 7 ≤ Nat.card F.Carrier)
    (e : generalizedFitting (coreQuotient H) ≃* PSL(2,F.Carrier))
    (hS : Nat.card d.quotientSylow ≤ 128) :
    Nonempty (generalizedFitting (coreQuotient H) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (generalizedFitting (coreQuotient H) ≃* SL(3,ZMod 2)) := by
  let a := d.source_ambientFittingEquivOffender hL
  let b := a.symm.trans e
  let P : Sylow 3 PSL(2,F.Carrier) := Classical.choice inferInstance
  let _ : Fact F.prime.Prime := ⟨F.prime_isPrime⟩
  have hr : primeRank 3 (generalizedFitting d.offenderGroup) ≤ 1 := by
    rw [primeRank_equiv 3 b]
    apply P.primeRank_le_one_of_isCyclic
    apply GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card
      F.Carrier F.card hseven 3 (by decide)
    rw [F.card]
    exact ((Nat.coprime_primes Nat.prime_three F.prime_isPrime).mpr
      (Ne.symm hp3)).pow_right F.degree
  rcases quasisimple_model_rank_one hr (c.fittingModel d.offenderAction) with
      ⟨B, ⟨eb⟩⟩ | ⟨B, hodd, ⟨eb⟩⟩
  · obtain ⟨ea⟩ := odd_linearTwo_binary_alternatingFive B
      ⟨F.prime, F.degree, F.prime_isPrime, ho, F.degree_pos, F.card⟩ eb b
    exact Or.inl ⟨a.trans ea⟩
  · exact Or.inr (linearThree_binary_equiv (generalizedFitting (coreQuotient H))
      B hodd (a.trans eb) d.quotientSylow hS)

private theorem source_large_odd_psl_component_impossible
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (F : FSource.FieldParameter) (ho : Odd F.prime) (hp3 : F.prime ≠ 3)
    (hnine : 9 ≤ Nat.card F.Carrier)
    (e : generalizedFitting (coreQuotient H) ≃* PSL(2,F.Carrier))
    (hS : Nat.card d.quotientSylow ≤ 128) : False := by
  have hodd : Odd (Nat.card F.Carrier) := by rw [F.card]; exact ho.pow
  have hl := pslTwo_order_ge_360 hodd hnine
  rcases d.source_odd_psl_component_models hL c F ho hp3 (by omega) e hS with ha | ha
  · obtain ⟨a⟩ := ha
    rw [Nat.card_congr (e.symm.trans a).toEquiv, nat_card_alternatingGroup] at hl
    norm_num [Nat.factorial] at hl
  · obtain ⟨a⟩ := ha
    rw [Nat.card_congr (e.symm.trans a).toEquiv, Matrix.PSL3Two.card_SL] at hl
    omega

private theorem source_prime_component_impossible
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (F : FSource.FieldParameter) (hn : F.degree = 1)
    (hm : F.prime % 24 = 11 ∨ F.prime % 24 = 13)
    (e : generalizedFitting (coreQuotient H) ≃* PSL(2,F.Carrier))
    (hS : Nat.card d.quotientSylow ≤ 128) : False := by
  apply d.source_large_odd_psl_component_impossible hL c F
    (Nat.odd_iff.mpr (by omega)) (by omega) _ e hS
  rw [F.card, hn, pow_one]
  omega

/-- F.6.18(4) is impossible on the original quotient and full offender action.
Both local labels have the same model, so either labeling supplies these data. -/
theorem source_component_row_four_impossible
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (F : FSource.FieldParameter) (hn : F.degree = 1)
    (hm : F.prime % 24 = 11 ∨ F.prime % 24 = 13)
    (e : coreQuotient H ≃* PSL(2,F.Carrier))
    (ht : generalizedFitting (coreQuotient H) = ⊤)
    (hs : Nonempty (d.quotientSylow ≃* FSource.E4))
    (_locals : Nonempty (d.G1.map coreProjection ≃* DihedralGroup 6) ∧
      Nonempty (d.G2.map coreProjection ≃* DihedralGroup 6)) : False := by
  obtain ⟨es⟩ := hs
  apply d.source_prime_component_impossible hL c F hn hm
    (((MulEquiv.subgroupCongr ht).trans topEquiv).trans e)
  rw [Nat.card_congr es.toEquiv]
  norm_num [FSource.E4, FSource.C, Nat.card_prod]

/-- F.6.18(5) is impossible in either local labeling. The ambient PGL₂
model, component model and both embedded local models are retained. -/
theorem source_component_row_five_impossible
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (F : FSource.FieldParameter) (hn : F.degree = 1)
    (hm : F.prime % 24 = 11 ∨ F.prime % 24 = 13)
    (_model : coreQuotient H ≃* PGL2 F.Carrier)
    (e : generalizedFitting (coreQuotient H) ≃* PSL(2,F.Carrier))
    (hs : Nonempty (d.quotientSylow ≃* DihedralGroup 4))
    (_locals :
      (Nonempty (d.G1.map coreProjection ≃* DihedralGroup 12) ∧
        Nonempty (d.G2.map coreProjection ≃* Equiv.Perm (Fin 4))) ∨
      (Nonempty (d.G2.map coreProjection ≃* DihedralGroup 12) ∧
        Nonempty (d.G1.map coreProjection ≃* Equiv.Perm (Fin 4)))) : False := by
  obtain ⟨es⟩ := hs
  apply d.source_prime_component_impossible hL c F hn hm e
  rw [Nat.card_congr es.toEquiv, DihedralGroup.nat_card]
  norm_num

/-- The actual offender action restricts the dihedral PSL₂ ambient group
to A₆ or SL₃(2), independently of the original local markings. -/
theorem source_component_dihedral_pslTwo_models
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (F : FSource.FieldParameter) (hn : F.degree ≤ 2)
    (hm : Nat.card F.Carrier % 16 = 7 ∨ Nat.card F.Carrier % 16 = 9)
    (e : coreQuotient H ≃* PSL(2,F.Carrier))
    (ht : generalizedFitting (coreQuotient H) = ⊤)
    (hs : Nonempty (d.quotientSylow ≃* DihedralGroup 4)) :
    Nonempty (coreQuotient H ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (coreQuotient H ≃* SL(3,ZMod 2)) := by
  by_cases hp3 : F.prime = 3
  · have hn' : F.degree = 1 ∨ F.degree = 2 := by have := F.degree_pos; omega
    have hc : Nat.card F.Carrier = 9 := by
      rcases hn' with hh | hh
      · have hc : Nat.card F.Carrier = 3 := by rw [F.card, hp3, hh, pow_one]
        omega
      · rw [F.card, hp3, hh]; decide
    exact Or.inl ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hc)⟩
  · obtain ⟨es⟩ := hs
    have hS : Nat.card d.quotientSylow ≤ 128 := by
      rw [Nat.card_congr es.toEquiv, DihedralGroup.nat_card]; norm_num
    have ho : Odd F.prime := by
      apply (Nat.odd_pow_iff (Nat.ne_of_gt F.degree_pos)).mp
      rw [← F.card, Nat.odd_iff]
      omega
    let et : generalizedFitting (coreQuotient H) ≃* coreQuotient H :=
      (MulEquiv.subgroupCongr ht).trans topEquiv
    rcases d.source_odd_psl_component_models hL c F ho hp3 (by omega) (et.trans e) hS with
      ha | ha
    · obtain ⟨a⟩ := ha
      have hodd : Odd (Nat.card F.Carrier) := by rw [F.card]; exact ho.pow
      have hl : 7 * (7 ^ 2 - 1) ≤ Nat.card PSL(2,F.Carrier) * 2 := by
        rw [Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice hodd]
        exact Nat.mul_le_mul (by omega)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega : 7 ≤ Nat.card F.Carrier) 2) 1)
      rw [Nat.card_congr (e.symm.trans (et.symm.trans a)).toEquiv,
        nat_card_alternatingGroup] at hl
      norm_num [Nat.factorial] at hl
    · obtain ⟨a⟩ := ha
      exact Or.inr ⟨et.symm.trans a⟩

/-- The ambient PSL₂ model with dihedral Sylow supplies all three terminal
outputs independently of the local-group markings. Away from
characteristic three the B-side component is SL₃(2); the remaining field has
nine elements and supplies the actual A₆ isomorphism. -/
theorem source_component_dihedral_pslTwo
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (F : FSource.FieldParameter) (hn : F.degree ≤ 2)
    (hm : Nat.card F.Carrier % 16 = 7 ∨ Nat.card F.Carrier % 16 = 9)
    (e : coreQuotient H ≃* PSL(2,F.Carrier))
    (ht : generalizedFitting (coreQuotient H) = ⊤)
    (hs : Nonempty (d.quotientSylow ≃* DihedralGroup 4)) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) := by
  rcases d.source_component_dihedral_pslTwo_models hL c F hn hm e ht hs with ha | he
  · exact d.component_row_alternatingSix hL ha.some
  · obtain ⟨ea⟩ := he
    let ex : (thompsonGroup H).map coreProjection ≃* SL(3,ZMod 2) :=
      ((MulEquiv.subgroupCongr (d.thompson_image_eq_top_of_fitting_top hL ht)).trans
        topEquiv).trans ea
    exact ⟨.linearThree ex, .linearThree ea, ComponentRows.quotient_of_fitting_top ht⟩

/-- All three terminal outputs for the PSL₂ half of F.6.18(6). Away from
characteristic three the B-side component is SL₃(2); the remaining field has
nine elements and supplies the actual A₆ isomorphism. -/
theorem source_component_row_six_pslTwo
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (F : FSource.FieldParameter) (hn : F.degree ≤ 2)
    (hm : Nat.card F.Carrier % 16 = 7 ∨ Nat.card F.Carrier % 16 = 9)
    (e : coreQuotient H ≃* PSL(2,F.Carrier))
    (ht : generalizedFitting (coreQuotient H) = ⊤)
    (hs : Nonempty (d.quotientSylow ≃* DihedralGroup 4))
    (_locals : Nonempty (d.G1.map coreProjection ≃* Equiv.Perm (Fin 4)) ∧
      Nonempty (d.G2.map coreProjection ≃* Equiv.Perm (Fin 4))) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) :=
  d.source_component_dihedral_pslTwo hL c F hn hm e ht hs

/-- An odd square-field component is restricted to characteristic three by
its genuine offender representation. Both split-sixteen source congruences
satisfy these hypotheses; no local-generator model enters the argument. -/
theorem source_square_psl_component_prime
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (F : FSource.FieldParameter) (hn : F.degree = 2) (ho : Odd F.prime)
    (e : generalizedFitting (coreQuotient H) ≃* PSL(2,F.Carrier))
    (hS : Nat.card d.quotientSylow ≤ 128) : F.prime = 3 := by
  by_contra hp3
  have hp := F.prime_isPrime.two_le
  have hpOdd := Nat.odd_iff.mp ho
  have hc : 9 ≤ Nat.card F.Carrier := by
    rw [F.card, hn]
    have h3 : 3 ≤ F.prime := by omega
    nlinarith
  exact d.source_large_odd_psl_component_impossible hL c F ho hp3 hc e hS

/-- The full B-side witness forces the prime in the field half of row (8)
to be three. The rank-one estimate is proved from the field torus theorem. -/
theorem source_component_row_eight_field_prime
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (r : FSource.FieldExtensionRow (D := coreQuotient H))
    (hs : Nonempty (d.quotientSylow ≃* (FSource.C 2 × DihedralGroup 4))) :
    r.field.prime = 3 := by
  have hm := r.congruence
  apply d.source_square_psl_component_prime hL c r.field r.degree
    (Nat.odd_iff.mpr (by omega)) r.componentEquiv
  obtain ⟨es⟩ := hs
  rw [Nat.card_congr es.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
  norm_num [FSource.C]

/-- All three outputs for the full field-extension half of F.6.18(8),
including the original Frobenius action and both local S₄ × C₂ models.
Swapping the local labels leaves `d` and its G₁-normalization unchanged. -/
theorem source_component_row_eight_field
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (r : FSource.FieldExtensionRow (D := coreQuotient H))
    (hs : Nonempty (d.quotientSylow ≃* (FSource.C 2 × DihedralGroup 4)))
    (_locals :
      Nonempty (d.G1.map coreProjection ≃* (FSource.C 2 × Equiv.Perm (Fin 4))) ∧
      Nonempty (d.G2.map coreProjection ≃* (FSource.C 2 × Equiv.Perm (Fin 4)))) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) := by
  have hp := d.source_component_row_eight_field_prime hL c r hs
  obtain ⟨es⟩ := hs
  obtain ⟨e⟩ := ComponentRows.OddFields.fieldRow_nine_equiv_symmetricSix
    r hp d.quotientSylow es
  have h := d.component_row_symmetricSix hL e
  exact ⟨h.1, h.2.1, ComponentRows.fieldRow_quotient r⟩

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
