module
public import Theory.SpecificGroups.Janko4.Model.IrreducibleCentralizer
public import Theory.Representation.BinaryConjugationSection.TrivialCommutant

/-!
# J₄ centralizers for a marked section with trivial commutant

The full-Sylow involution-centralizer argument also applies to reducible
sections with trivial invertible commutant. The first centralizer forces
the entire fully moved subgroup into its core center of order two; the
second cannot contain a full Sylow. Hence its actor has odd centralizer.

The literal binary natural-plus-dual section supplies the commutant premise
in Aschbacher--Smith 10.2.9, printed pp.750--751.
-/

public noncomputable section
namespace Janko4
open Subgroup Theory.GroupTheory InvolutionCentralizers
attribute [local irreducible] modelGroup matrixA matrixB
theorem centralizer_odd_of_trivial_commutant_section
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (S : Sylow 2 Model) (B E : Subgroup Model) [IsElementaryAbelian 2 E]
    {ρ : Representation (ZMod 2) B W}
    (d : Representation.BinaryConjugationSection B E (E ⊓ centralizer (B : Set Model)) ρ)
    (htriv : ∀ f : W ≃ₗ[ZMod 2] W, (∀ b w, f (ρ b w) = ρ b (f w)) →
      f = LinearEquiv.refl _ _)
    (hSB : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (hSE : (S : Subgroup Model) ≤ normalizer (E : Set Model))
    (hc : 2 < Nat.card E)
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set Model)) (hmove : ⁅E,B⁆ = E) :
    ¬ 2 ∣ Nat.card (centralizer (B : Set Model)) := by
  intro heven
  obtain ⟨z,hz,h⟩ := exists_involution_centralizing_normalizing_two_group
    B (S : Subgroup Model) S.isPGroup' hSB heven
  let K := centralizer ({z} : Set Model)
  have hBK : B ≤ K := le_sup_left.trans h
  have hSK : (S : Subgroup Model) ≤ K := le_sup_right.trans h
  rcases centralizer_equiv_first_or_second z hz with hfirst | hsecond
  · obtain ⟨e⟩ := hfirst
    have hbound := d.card_le_overgroup_core_center_of_trivial_commutant
      htriv S hSB hSE hcore hmove K hBK hSK
      (centralizer_characteristic_two z hz)
    let eP : pCore 2 K ≃* pCore 2 First.centralizer :=
      (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
    have hcc := Nat.card_congr (centerCongr eP).toEquiv
    let := First.centralizer_twoCore_extraspecial
    rw [IsExtraspecial.center_order_p 2 (pCore 2 First.centralizer)] at hcc
    omega
  · obtain ⟨e⟩ := hsecond
    have hdiv : 2^21 ∣ Nat.card S := by
      have hd : 2^21 ∣ Nat.card Model := by rw [Cardinality.model_card]; norm_num
      rw [←(S : Subgroup Model).card_mul_index] at hd
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr S.not_dvd_index).pow_left 21
        |>.dvd_of_dvd_mul_right hd
    have hd := hdiv.trans (card_dvd_of_le hSK)
    rw [Nat.card_congr e.toEquiv,Second.ambient_card] at hd
    norm_num at hd

end Janko4
