module

public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.GLTwoThreeInvolutions

/-!
# Inversion in a faithful elementary four-on-nine action

An elementary abelian group of order four acting faithfully on an
elementary abelian group of order nine contains an element acting by
inversion. Both cardinalities and faithfulness concern the specified
action; no alternate action or ambient normalizer is introduced.

The module becomes a two-dimensional vector space over the field of three
elements. Its faithful representation sends two distinct nonidentity
actors to commuting involutions. The finite two-by-two matrix lemma puts
scalar minus one among their images. The matrix algebra equivalence and
the additive/multiplicative type-tag transport turn that scalar into
inversion of the original group.

This standard coprime action observation supplies the central inversion
element in the group-identification step of Stellmacher (1.6), journal
p.18; see `refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative

namespace Representation

/-- A faithful elementary four-on-nine action contains inversion. -/
public theorem exists_inversion_of_elementary_card_four_card_nine
    {A W : Type*} [Group A] [Group W] [Finite A] [Finite W]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 3 W]
    [MulDistribMulAction A W]
    (hA : Nat.card A = 4) (hW : Nat.card W = 9)
    (hfaith : fixingSubgroup A (Set.univ : Set W) = ⊥) :
    ∃ z : A, z ≠ 1 ∧ ∀ w : W, z • w = w⁻¹ := by
  classical
  let ρ := Representation.ofElementaryAbelianAction (A := A) (G := W) (p := 3)
  have hρinj : Function.Injective ρ.asGroupHom := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro a ha
    have heq : ρ a = 1 := congrArg Units.val (MonoidHom.mem_ker.mp ha)
    have hafix : a ∈ fixingSubgroup A (Set.univ : Set W) := by
      rw [mem_fixingSubgroup_iff]
      intro w _
      apply Additive.ofMul.injective
      have hw := LinearMap.congr_fun heq (Additive.ofMul w)
      simpa only [ρ, Representation.ofElementaryAbelianAction_apply_ofMul,
        Module.End.one_apply] using hw
    exact hfaith.le hafix
  have hdim : Module.finrank (ZMod 3) (Additive W) = 2 := by
    have hc : Nat.card (Additive W) = 9 := (Nat.card_congr Additive.toMul).trans hW
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3)] at hc
    norm_num at hc
    exact Nat.pow_right_injective (by omega : 1 < 3) hc
  let bas : Module.Basis (Fin 2) (ZMod 3) (Additive W) :=
    Module.finBasisOfFinrankEq (ZMod 3) (Additive W) hdim
  let m := LinearMap.toMatrixAlgEquiv bas
  let μ : A →* Matrix (Fin 2) (Fin 2) (ZMod 3) := m.toMonoidHom.comp ρ
  have hμinj : Function.Injective μ := by
    intro a b hab
    apply hρinj
    apply Units.ext
    exact m.injective hab
  let _ : Fintype A := Fintype.ofFinite A
  let _ : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  have hAthree : 3 ≤ ENat.card A := by
    rw [ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card, hA]
    decide
  obtain ⟨b, hb, hba⟩ := ENat.exists_ne_ne_of_three_le hAthree 1 a
  have hsq (x : A) : x * x = 1 := by
    have hx := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) x
    simpa only [pow_two] using hx
  have hμsq (x : A) : μ x * μ x = 1 := by rw [← map_mul, hsq, map_one]
  have hμcomm : μ a * μ b = μ b * μ a := by rw [← map_mul, ← map_mul, mul_comm]
  have hμa : μ a ≠ 1 := fun heq => ha (hμinj (heq.trans μ.map_one.symm))
  have hμb : μ b ≠ 1 := fun heq => hb (hμinj (heq.trans μ.map_one.symm))
  have hμab : μ a ≠ μ b := fun heq => hba (hμinj heq).symm
  have hneg : ∃ z : A, μ z = -1 := by
    rcases Matrix.commuting_distinct_involutions_two_three_neg_one
      (μ a) (μ b) (hμsq a) (hμsq b) hμcomm hμa hμb hμab with h | h | h
    · exact ⟨a, h⟩
    · exact ⟨b, h⟩
    · exact ⟨a * b, by simpa only [map_mul] using h⟩
  obtain ⟨z, hz⟩ := hneg
  have hρz : ρ z = -1 := by
    apply m.injective
    change μ z = m (-1)
    rw [map_neg, map_one]
    exact hz
  refine ⟨z, ?_, ?_⟩
  · intro hz1
    have hbad : (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) = -1 := by
      simpa only [hz1, map_one] using hz
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod 3) => M 0 0) hbad
    have hbad' : (1 : ZMod 3) = -1 := by simpa using hentry
    exact (by decide : (1 : ZMod 3) ≠ -1) hbad'
  · intro w
    apply Additive.ofMul.injective
    have hw := LinearMap.congr_fun hρz (Additive.ofMul w)
    simpa only [ρ, Representation.ofElementaryAbelianAction_apply_ofMul,
      LinearMap.neg_apply, Module.End.one_apply, ofMul_inv] using hw

end Representation

