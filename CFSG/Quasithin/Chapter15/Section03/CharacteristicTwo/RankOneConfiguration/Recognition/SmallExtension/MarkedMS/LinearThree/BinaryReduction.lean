module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Classification.Models
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Conditions
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs.FieldTransport

/-!
# The binary field forced by the small MS quotient

The three permitted central-core quotients have orders 168, 360 and 6048.
A projective SL₃(2ⁿ) quotient contains the literal upper-unipotent subgroup
of order 2^(3n). Since 64 divides none of those three orders, n is one.
This argument uses the quotient part of MS1 only, and therefore applies
to every SmallMSPair, without a chosen Chapter 15 parabolic marking.

The final theorem transports all five module alternatives from the binary
field to the requested field of order 2ⁿ. It retains all original source
clauses and the single common marking; exhaustiveness over the binary
field remains a separate mathematical obligation.

Source: Aschbacher--Smith C.1.31--34, printed pp.135--137.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

theorem SmallRankTwoQuotient.card {L : Type*} [Group L] (h : SmallRankTwoQuotient L) :
    Nat.card (L ⧸ centralPreimage (pCore 2 L)) = 168 ∨
    Nat.card (L ⧸ centralPreimage (pCore 2 L)) = 360 ∨
    Nat.card (L ⧸ centralPreimage (pCore 2 L)) = 6048 := by
  unfold SmallRankTwoQuotient at h
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    left
    let := Atlas.sl_perfect 3 (by decide) (F := ZMod 2)
    rw [Nat.card_congr e.toEquiv, Group.IsPerfect.commutator_eq_top, Subgroup.card_top]
    exact Matrix.PSL3Two.card_SL
  · obtain ⟨e⟩ := h
    right; left
    rw [Nat.card_congr (e.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp))).toEquiv,
      nat_card_alternatingGroup]
    norm_num
  · obtain ⟨e⟩ := h
    right; right
    rw [Nat.card_congr e.toEquiv, Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      Atlas.G2.BinaryException.card_H]

private def quotientCenterEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro x hx
      exact ⟨e.symm x, (centerCongr e).symm ⟨x, hx⟩ |>.property,
        e.apply_symm_apply x⟩)

theorem SmallRankTwoQuotient.linearThree_degree {L : Type*} [Group L] (h : SmallRankTwoQuotient L)
    (n : ℕ) (hn : 1 ≤ n) (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F) : n = 1 := by
  let f := (centralPreimageQuotientEquiv (pCore 2 L)).trans (quotientCenterEquiv e)
  have hd : 2 ^ (n * 3) ∣ Nat.card (L ⧸ centralPreimage (pCore 2 L)) := by
    rw [Nat.card_congr f.toEquiv, pow_mul, ← hF,
      ← Matrix.PSL3.LinearThree.card_unipotent F]
    exact card_subgroup_dvd_card (Matrix.PSL3.LinearThree.unipotent F)
  by_contra hne
  have h64 : 64 ∣ Nat.card (L ⧸ centralPreimage (pCore 2 L)) :=
    (pow_dvd_pow 2 (show 6 ≤ n * 3 by omega)).trans hd
  rcases SmallRankTwoQuotient.card h with hc | hc | hc <;> rw [hc] at h64 <;>
    norm_num at h64


/-- The full field parameter is forced already by the small quotient condition. -/
theorem SmallMSPair.linearThree_binary {G : Type*} [Group G] {κ : GroupClass}
    {L R : Subgroup G} (h : SmallMSPair κ L R)
    (n : ℕ) (hn : 1 ≤ n) (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F) :
    n = 1 ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have hn1 := h.rankTwo.linearThree_degree n hn F hF e
  refine ⟨hn1, ?_⟩
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [hn1, pow_one, Nat.card_eq_fintype_card] using hF)).symm
  exact ⟨e.trans (Atlas.fieldEquivSL 3 f)⟩

/-- Apply a binary source classification at the literal pair, then transport
all five alternatives to the field requested by the universal interface. -/
theorem SmallMSPair.linearThree_of_binary {G : Type*} [Group G] {κ : GroupClass}
    {L R S : Subgroup G} (h : SmallMSPair κ L R)
    (n : ℕ) (hn : 1 ≤ n) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n)
    (he : Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F))
    (binary : Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        MSModuleAlternatives L R S 1 (ZMod 2) e) :
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F,
      MSModuleAlternatives L R S n F e := by
  obtain ⟨e⟩ := he
  obtain ⟨hn1, hbin⟩ := h.linearThree_binary n hn F hF e
  subst n
  obtain ⟨e0, h0⟩ := binary hbin
  let := Fintype.ofFinite F
  let f : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [pow_one, Nat.card_eq_fintype_card] using hF)
  exact ⟨e0.trans (Atlas.fieldEquivSL 3 f), h0.fieldTransport f⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
