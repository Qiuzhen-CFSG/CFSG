module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NoFF
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.AtlasPort.LinearGroups.G2.Order

/-!
# Distinguishing SL₃(4) in the full B.4.2 action list

The actual SL₃(4) group has order 60480 and center of order three. Center
orders exclude the rank-two linear, symplectic, and binary higher-rank
linear models. Group orders exclude the alternating groups and triple cover;
the G₂ order formula excludes the full groups and even bounds their binary
derived subgroup. For SL₃(2ⁿ), divisibility of the order by 2^(3n) gives n ≤ 2,
and the center excludes n = 1. Thus only the natural action over a field of
order four survives. Every comparison uses the supplied group equivalence.

Source: Aschbacher–Smith, B.4.2, printed p.86, as invoked by B.5.1(1i),
printed pp.99–103, combined manuscript of 1 March 2004. Order and center
formulas reuse the attributed ATLAS ports imported below; no ATLAS source
is copied here.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.SL3FourNaturalDual
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NoFF.Recognition

private lemma field_card : Nat.card F = 4 := by
  rw [Nat.card_eq_fintype_card]
  exact SL2FourNatural.card_field

private lemma center_card : Nat.card (center SL) = 3 := by
  rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin, field_card]
  decide

private lemma sl_card : Nat.card SL = 60480 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [field_card] at h
  norm_num [Fin.prod_univ_succ] at h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL), center_card]
  change Nat.card PSL(3,F) * 3 = 60480
  rw [Nat.card_eq_fintype_card]
  omega

private lemma not_linearTwo (E : BinaryField) (e : SL ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) : False := by
  have h := Nat.card_congr (centerCongr e).toEquiv
  rw [center_card, Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin] at h
  have hd := Nat.gcd_dvd_left 2 (Nat.card E.Carrier - 1)
  rw [← h] at hd
  norm_num at hd

lemma linearThree_card (E : BinaryField)
    (e : SL ≃* Matrix.SpecialLinearGroup (Fin 3) E.Carrier) : Nat.card E.Carrier = 4 := by
  have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 3) E.Carrier) = 60480 :=
    (Nat.card_congr e.toEquiv).symm.trans sl_card
  have hd : Nat.card E.Carrier ^ 3 ∣ 60480 := by
    rw [← hc]
    exact (Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card (F := E.Carrier)).trans
      (card_quotient_dvd_card (center (Matrix.SpecialLinearGroup (Fin 3) E.Carrier)))
  have hdeg : E.degree ≤ 2 := by
    by_contra hn
    have hp : 2 ^ 9 ∣ 60480 := by
      apply dvd_trans _ hd
      rw [E.card_eq, ← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    norm_num at hp
  have hz := Nat.card_congr (centerCongr e).toEquiv
  rw [center_card, Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin, E.card_eq] at hz
  have hpos := E.degree_pos
  have htwo : E.degree = 2 := by
    by_contra hn
    have he : E.degree = 1 := by omega
    norm_num [he] at hz
  norm_num [E.card_eq, htwo]

private lemma not_symplectic (E : BinaryField)
    (e : SL ≃* Matrix.symplecticGroup (Fin 2) E.Carrier) : False := by
  have h := Nat.card_congr (centerCongr e).toEquiv
  rw [center_card, Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot,
    Subgroup.card_bot] at h
  contradiction

private lemma not_g2 (E : BinaryField) (e : SL ≃* Atlas.G2.Model E.Carrier) : False := by
  have hc : Nat.card (Atlas.G2.Model E.Carrier) = 60480 :=
    (Nat.card_congr e.toEquiv).symm.trans sl_card
  rw [Atlas.G2.card_Model, E.card_eq] at hc
  have hd : (2 ^ E.degree) ^ 6 ∣ 60480 := by
    rw [← hc]
    exact dvd_mul_right _ _ |>.trans (dvd_mul_right _ _)
  have hdeg : E.degree ≤ 1 := by
    by_contra hn
    have hp : 2 ^ 12 ∣ 60480 := by
      apply dvd_trans _ hd
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    norm_num at hp
  have he : E.degree = 1 := by have := E.degree_pos; omega
  norm_num [he] at hc

private lemma not_alternating (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (e : SL ≃* alternatingGroup (Fin n)) : False := by
  have h := Nat.card_congr e.toEquiv
  rw [sl_card] at h
  rcases hn with rfl | rfl | rfl | rfl <;>
    rw [nat_card_alternatingGroup, Nat.card_fin] at h <;> norm_num at h

lemma not_binaryLinear (d : ℕ) (hd : d = 4 ∨ d = 5)
    (e : SL ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) : False := by
  have h := Nat.card_congr (centerCongr e).toEquiv
  rcases hd with rfl | rfl <;>
    rw [center_card, Atlas.ExceptionalSupport.card_sl_center] at h <;> norm_num at h

private lemma not_g2Derived (e : SL ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hd := (commutator (Atlas.G2.Model (ZMod 2))).card_subgroup_dvd_card
  rw [← Nat.card_congr e.toEquiv, sl_card, Atlas.G2.card_Model, Nat.card_zmod] at hd
  norm_num at hd

private lemma not_tripleSix {L : Type*} [Group L] [Finite L] (e : L ≃* SL)
    (z : center L ≃* Multiplicative (ZMod 3))
    (q : (L ⧸ center L) ≃* alternatingGroup (Fin 6)) : False := by
  have hc : Nat.card L = 60480 := (Nat.card_congr e.toEquiv).trans sl_card
  have hz : Nat.card (center L) = 3 := (Nat.card_congr z.toEquiv).trans (Nat.card_zmod 3)
  have hq : Nat.card (L ⧸ center L) = 360 := by
    rw [Nat.card_congr q.toEquiv, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
  rw [hc, hz, hq] at hh
  contradiction


universe u v
variable {D : Type u} [Group D] [Finite D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The complete B.4.2 list leaves the genuine degree-three natural action over four elements. -/
theorem irreducible_linearThree {L H : Subgroup D} (eL : L ≃* SL)
    (h : IrreducibleActionCase ρ L H) :
    ∃ E : BinaryField, Nat.card E.Carrier = 4 ∧
      Nonempty (ActionEquiv (ρ.comp L.subtype) (linearNatural E 3)) := by
  cases h with
  | linearTwo E _ e _ _ => exact (not_linearTwo E (eL.symm.trans e.groupEquiv)).elim
  | linearThree E _ e _ => exact ⟨E, linearThree_card E (eL.symm.trans e.groupEquiv), ⟨e⟩⟩
  | symplectic E _ _ e _ => exact (not_symplectic E (eL.symm.trans e.groupEquiv)).elim
  | symplecticTwo e _ =>
    exact (not_alternating 6 (Or.inr (Or.inl rfl))
      (eL.symm.trans (e.subgroupEquiv.trans binarySymplecticDerivedEquiv))).elim
  | g2 E _ _ e _ _ => exact (not_g2 E (eL.symm.trans e.groupEquiv)).elim
  | g2Two e _ _ => exact (not_g2Derived (eL.symm.trans e.subgroupEquiv)).elim
  | symmetric n hn e _ _ =>
    apply (not_alternating n ?_ (eL.symm.trans e.subgroupEquiv)).elim
    rcases hn with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
  | alternatingSix _ e _ _ =>
    exact (not_alternating 6 (Or.inr (Or.inl rfl)) (eL.symm.trans e.groupEquiv)).elim
  | alternatingSeven _ _ e _ _ _ =>
    exact (not_alternating 7 (Or.inr (Or.inr (Or.inl rfl))) (eL.symm.trans e)).elim
  | tripleSix _ a _ => exact (not_tripleSix eL a.centerEquiv a.quotientEquiv).elim
  | binaryLinear d hd _ e _ => exact (not_binaryLinear d hd (eL.symm.trans e.groupEquiv)).elim
  | orthogonalSix _ _ e _ _ =>
    exact (not_alternating 8 (Or.inr (Or.inr (Or.inr rfl))) (eL.symm.trans e.groupEquiv)).elim
  | symmetricEight _ e _ =>
    exact (not_alternating 8 (Or.inr (Or.inr (Or.inr rfl))) (eL.symm.trans e.subgroupEquiv)).elim
  | exteriorFive _ _ e _ _ _ => exact (not_binaryLinear 5 (Or.inr rfl) (eL.symm.trans e)).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NoFF.Recognition
