module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ElementarySylowEight.Bounds
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SmallModels
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# The small elementary-Sylow sieve on the marked B.5 group models

The source classification retains group equivalences. Elementary Sylow
subgroups of order at most eight exclude all but the binary rank-one rows;
the surviving field has order four or eight. No model is assumed for an
ambient overgroup or for an original full two-core.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction.ElementarySylowEight
open QuasisimpleSource
variable {D : Type*} [Group D] [Finite D]

private def fieldTwoEquiv (F : BinaryField) (h : F.degree = 1) :
    F.Carrier ≃+* ZMod 2 := by
  let : Fintype F.Carrier := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,F.card_eq,h]; simp)

theorem linearTwo_degree_le_three (h : Bound D) (F : BinaryField)
    (e : D ≃* SL(2,F.Carrier)) : F.degree ≤ 3 := by
  apply h.two_power_le
  rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,F.card_eq]
  exact dvd_mul_right _ _

theorem no_linearThree (h : Bound D) (F : BinaryField)
    (e : D ≃* SL(3,F.Carrier)) : False := by
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,←pow_mul] at hd
  have hb := h.two_power_le (n := 3 * F.degree) (by
    rw [Nat.card_congr e.toEquiv]; simpa only [Nat.mul_comm] using hd)
  have h1 : F.degree = 1 := by have := F.degree_pos; omega
  let f := e.trans ((Atlas.fieldEquivSL 3 (fieldTwoEquiv F h1)).trans Matrix.PSL3Two.equiv)
  exact no_psl_three_two (h.of_surjective f.toMonoidHom f.surjective)

theorem no_linearFourTwo (h : Bound D) (e : D ≃* SL(4,ZMod 2)) : False := by
  apply h.not_sixteen_dvd
  rw [Nat.card_congr e.toEquiv,Atlas.Order20160A8.sl4Two_card]
  decide

theorem no_g2DerivedTwo (h : Bound D)
    (e : D ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  apply h.not_sixteen_dvd
  rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
  decide

theorem no_symmetric_five (h : Bound (Equiv.Perm (Fin 5))) : False := by
  let x : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3
  apply h.no_order_four x
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 4)
  · decide +kernel
  · intro p hp hd
    have hp2 : p = 2 := by
      have hp' := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hd)
      exact (Nat.dvd_prime Nat.prime_two).mp hp' |>.resolve_left hp.ne_one
    subst p
    decide +kernel

theorem linearTwo_four_equiv (F : BinaryField) (hf : F.degree = 2) :
    Nonempty (SL(2,F.Carrier) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := F.Carrier) (by rw [F.card_eq,hf]; decide)
  exact ⟨Atlas.RankOneFieldAutomorphisms.slEquivPSL.trans e⟩

/-- The marked quasisimple catalogue has only its two small rank-one rows. -/
theorem smallModel_rank_one (h : Bound D) (m : ChapterC.C27Source.SmallModels.Model D) :
    ∃ F : BinaryField, (F.degree = 2 ∨ F.degree = 3) ∧ Nonempty (D ≃* SL(2,F.Carrier)) := by
  cases m with
  | linearTwo F lo _ e =>
    have hi := linearTwo_degree_le_three h F e
    exact ⟨F,by omega,⟨e⟩⟩
  | linearThree F _ e => exact (no_linearThree h F e).elim
  | alternatingSix e => exact (no_alternating_six (h.of_surjective e.toMonoidHom e.surjective)).elim
  | alternatingSeven e => exact (no_alternating_seven (h.of_surjective e.toMonoidHom e.surjective)).elim
  | tripleSix _ e =>
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center D))
    exact (no_alternating_six (h.of_surjective f
      (e.surjective.comp (QuotientGroup.mk'_surjective _)))).elim
  | g2DerivedTwo e => exact (no_g2DerivedTwo h e).elim
  | linearFourTwo e => exact (no_linearFourTwo h e).elim

/-- Divisibility by five selects the actual four-field marking. -/
theorem smallModel_five (h : Bound D) (m : ChapterC.C27Source.SmallModels.Model D)
    (hf : 5 ∣ Nat.card D) : Nonempty (D ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,hF,⟨e⟩⟩ := smallModel_rank_one h m
  rcases hF with hF | hF
  · obtain ⟨a⟩ := linearTwo_four_equiv F hF
    exact ⟨e.trans a⟩
  · rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,F.card_eq,hF] at hf
    norm_num at hf

end CFSG.Quasithin.ChapterB.SourceInduction.ElementarySylowEight
