module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Three.SylowData
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Base
public import Theory.GroupTheory.SylowElementConjugacy
import Mathlib.Tactic.FinCases

/-!
# The two cubic classes in the literal Hall--Janko carrier

Twenty-seven certified normal forms are closed under multiplication and inverse,
and are distinct. Their cardinality is the full three-part of 604800, so they
form a Sylow subgroup. Checked carrier conjugators take each nonidentity row to
representative 1 or 7. Sylow conjugacy gives the exhaustive cubic fusion theorem.

Each product is checked on the existing four-point base. Separate row checks
bound kernel reduction memory; declaration elaboration is sequential here.
Source: ATLAS `J2G1-p100B0` normal forms; witness provenance and reproduction
are in `Three/source/README.md`. GAP's Sylow and fusion computations only find
witnesses: the subgroup, its order and all conjugacy equations are proved here.
-/

namespace Sporadic.LeechRelated.J2.PowerFusionCertificate
open GeneratorPair.SecondOrbitCertificate ThreeCertificates

set_option Elab.async false

private def sylowElement (i : Fin 27) : Carrier := element (sylowIndex i)

private def MulRow (i : Fin 27) : Prop := ∀ j : Fin 27, ∀ k : Fin 4,
    normalForm (sylowIndex i) (normalForm (sylowIndex j) (k.castLE (by decide))) =
    normalForm (sylowIndex (sylowMul i j)) (k.castLE (by decide))

private theorem mulRow00 : MulRow 0 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow01 : MulRow 1 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow02 : MulRow 2 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow03 : MulRow 3 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow04 : MulRow 4 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow05 : MulRow 5 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow06 : MulRow 6 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow07 : MulRow 7 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow08 : MulRow 8 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow09 : MulRow 9 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow10 : MulRow 10 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow11 : MulRow 11 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow12 : MulRow 12 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow13 : MulRow 13 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow14 : MulRow 14 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow15 : MulRow 15 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow16 : MulRow 16 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow17 : MulRow 17 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow18 : MulRow 18 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow19 : MulRow 19 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow20 : MulRow 20 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow21 : MulRow 21 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow22 : MulRow 22 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow23 : MulRow 23 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow24 : MulRow 24 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow25 : MulRow 25 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem mulRow26 : MulRow 26 := by
  unfold MulRow
  apply allFin
  decide +kernel

private theorem sylow_mul_check (i : Fin 27) : MulRow i := by
  fin_cases i
  · exact mulRow00
  · exact mulRow01
  · exact mulRow02
  · exact mulRow03
  · exact mulRow04
  · exact mulRow05
  · exact mulRow06
  · exact mulRow07
  · exact mulRow08
  · exact mulRow09
  · exact mulRow10
  · exact mulRow11
  · exact mulRow12
  · exact mulRow13
  · exact mulRow14
  · exact mulRow15
  · exact mulRow16
  · exact mulRow17
  · exact mulRow18
  · exact mulRow19
  · exact mulRow20
  · exact mulRow21
  · exact mulRow22
  · exact mulRow23
  · exact mulRow24
  · exact mulRow25
  · exact mulRow26

private theorem sylowElement_zero : sylowElement 0 = 1 := representative_zero

private theorem sylowElement_mul (i j : Fin 27) :
    sylowElement i * sylowElement j = sylowElement (sylowMul i j) := by
  apply carrier_ext_base
  exact sylow_mul_check i j

private theorem sylow_inv_check : ∀ i : Fin 27, sylowMul i (sylowInv i) = 0 := by
  decide +kernel

private theorem sylowElement_inv (i : Fin 27) :
    sylowElement (sylowInv i) = (sylowElement i)⁻¹ := by
  apply mul_left_cancel (a := sylowElement i)
  rw [sylowElement_mul, sylow_inv_check, sylowElement_zero, mul_inv_cancel]

private theorem sylowElement_injective : Function.Injective sylowElement := by
  intro i j h
  have hi : sylowIndex i = sylowIndex j :=
    ExceptionalParabolics.FirstParabolic.normalForm_injective (congrArg inclusion h)
  exact (by decide +kernel : Function.Injective sylowIndex) hi

private def threeGroup : Subgroup Carrier where
  carrier := Set.range sylowElement
  one_mem' := ⟨0, sylowElement_zero⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨sylowMul i j, (sylowElement_mul i j).symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨sylowInv i, sylowElement_inv i⟩

private theorem card_threeGroup : Nat.card threeGroup = 27 := by
  let e : Fin 27 ≃ threeGroup := Equiv.ofBijective (fun i => ⟨sylowElement i, ⟨i, rfl⟩⟩)
    ⟨fun i j h => sylowElement_injective (congrArg Subtype.val h), by
      rintro ⟨x, i, rfl⟩
      exact ⟨i, rfl⟩⟩
  exact (Nat.card_congr e.symm).trans (Nat.card_fin 27)

private instance three_prime : Fact (Nat.Prime 3) := ⟨by decide⟩

private def threeSylow : Sylow 3 Carrier :=
  (IsPGroup.of_card (n := 3) card_threeGroup).toSylow (by
    have h := threeGroup.card_mul_index
    rw [card_threeGroup, ExceptionalParabolics.FirstParabolic.card_carrier] at h
    have hi : threeGroup.index = 22400 := by omega
    rw [hi]
    decide)

private theorem sylow_fusion_check : ∀ i : Fin 27, i ≠ 0 → ∀ k : Fin 4,
    normalForm (fusionConjugator i)
      (normalForm (representativeIndex (fusionClass i)) (k.castLE (by decide))) =
    normalForm (sylowIndex i)
      (normalForm (fusionConjugator i) (k.castLE (by decide))) := by
  apply allFin
  decide +kernel

private theorem sylowElement_fusion (i : Fin 27) (hi : i ≠ 0) :
    IsConj (representative 1) (sylowElement i) ∨
      IsConj (representative 7) (sylowElement i) := by
  have h : IsConj (representative (fusionClass i)) (sylowElement i) := by
    apply isConj_of_base _ _ (element (fusionConjugator i))
    exact sylow_fusion_check i hi
  have hc : fusionClass i = 1 ∨ fusionClass i = 7 := by
    unfold fusionClass
    split_ifs <;> simp
  rcases hc with hc | hc
  · exact Or.inl (hc ▸ h)
  · exact Or.inr (hc ▸ h)

/-- Every nonidentity element of three-power order is conjugate, inside the
literal carrier, to one of the two designated cubic representatives. -/
public theorem three_power_fusion (x : Carrier) {n : ℕ}
    (hx : orderOf x = 3 ^ n) (hne : x ≠ 1) :
    IsConj (representative 1) x ∨ IsConj (representative 7) x := by
  obtain ⟨y, hy⟩ := threeSylow.exists_isConj_of_orderOf_eq_prime_pow hx
  obtain ⟨i, hi⟩ := y.property
  have hi0 : i ≠ 0 := by
    intro he
    have hy1 : (y : Carrier) = 1 := hi.symm.trans (he ▸ sylowElement_zero)
    obtain ⟨c, hc⟩ := isConj_iff.mp hy
    have hx1 : x = 1 := (MulAut.conj c).injective
      (show MulAut.conj c x = MulAut.conj c 1 from
        hc.trans (hy1.trans (map_one _).symm))
    exact hne hx1
  rcases sylowElement_fusion i hi0 with h | h
  · exact Or.inl ((hi ▸ h).trans hy.symm)
  · exact Or.inr ((hi ▸ h).trans hy.symm)

/-- Every element of order three is conjugate to a designated cubic representative. -/
public theorem three_fusion (x : Carrier) (hx : orderOf x = 3) :
    IsConj (representative 1) x ∨ IsConj (representative 7) x :=
  three_power_fusion x (hx.trans (pow_one 3).symm) (by
    intro h
    simp [h] at hx)

/-- Three-power order is enough for coverage; this also handles the identity. -/
public theorem covered_of_three_power (g : Carrier) {n : ℕ}
    (hg : orderOf g = 3 ^ n) : ∃ i : Fin 21, IsConj (representative i) g := by
  by_cases h : g = 1
  · exact ⟨0, by rw [h, representative_zero]⟩
  rcases three_power_fusion g hg h with h | h
  · exact ⟨1, h⟩
  · exact ⟨7, h⟩

/-- The first designated cubic representative has order exactly three. -/
public theorem representative_one_order : orderOf (representative 1) = 3 := by
  apply orderOf_eq_prime
  · apply carrier_ext_base
    decide +kernel
  · intro h
    have he := congrArg (fun g : Carrier => inclusion g 0) h
    exact (by decide +kernel : inclusion (representative 1) 0 ≠ 0) he

/-- The second designated cubic representative has order exactly three. -/
public theorem representative_seven_order : orderOf (representative 7) = 3 := by
  apply orderOf_eq_prime
  · apply carrier_ext_base
    decide +kernel
  · intro h
    have he := congrArg (fun g : Carrier => inclusion g 0) h
    exact (by decide +kernel : inclusion (representative 7) 0 ≠ 0) he

/-- The cubic-order subcase of exhaustive representative coverage. -/
public theorem covered_of_order_three (g : Carrier) (hg : orderOf g = 3) :
    ∃ i : Fin 21, IsConj (representative i) g := by
  rcases three_fusion g hg with h | h
  · exact ⟨1, h⟩
  · exact ⟨7, h⟩

end Sporadic.LeechRelated.J2.PowerFusionCertificate
