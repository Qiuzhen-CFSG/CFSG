module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.ActorCertificates.Fusion
/-!
# Local centralizer and two-core escape certificates

The three fused actors commute with the marked graph involution. Their
centralizers inside the explicit Sylow also commute with that marker.
Each actor contains an inner involution whose commutator with a fixed
local element is a nonidentity cubic. Normality and the proved order eight
of the intrinsic local two-core exclude that involution from the core.

Source: Aschbacher–Smith E.1.2 and E.1.5, printed pp.209–210,
and E.1.14(7), printed p.214; Asc82a Lemma 4.11.
-/

public section
set_option maxRecDepth 10000
open Subgroup Matrix.PSL3Three Matrix.PSL3Three.GraphLocalQuotients
open Matrix.PSL3.OuterSolvable
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.ActorCertificates

@[expose] def escapeIndex (n : Fin 15) : Index :=
  (if target n = 6 then 8 else 12, false)

theorem escape_mem : ∀ n : Fin 15, escapeIndex n ∈ actor (target n) := by
  decide +kernel

theorem target_local : ∀ (n : Fin 15) (i : Index),
    i ∈ actor (target n) → commutes i (13,true) := by
  decide +kernel

theorem target_centralizer : ∀ (n : Fin 15) (i : Index),
    (∀ j ∈ actor (target n), commutes i j) → commutes i (13,true) := by
  decide +kernel

@[expose] def cubicMatrix : SL := ⟨!![0,0,2; 2,2,1; 2,0,0], by decide⟩

private theorem cubic_conjugates_marker :
    (MulAut.conj (inner cubicMatrix)) (element (13,true)) = element (13,true) := by
  rw [element, conjugate_pair]
  have hm : cubicMatrix * twoElement 13 *
      Matrix.SpecialLinearGroup.transpose cubicMatrix = twoElement 13 := by
    apply Subtype.ext
    decide +kernel
  change pair (cubicMatrix * twoElement 13 *
    Matrix.SpecialLinearGroup.transpose cubicMatrix) true = _
  rw [hm]

abbrev K := localSubgroup (localConjugator true)

theorem cubic_mem_local : inner cubicMatrix ∈ K := by
  rw [K, localSubgroup_marker]
  apply mem_centralizer_singleton_iff.mpr
  exact mul_inv_eq_iff_eq_mul.mp cubic_conjugates_marker

@[expose] def cubicCommutator (n : Fin 15) : SL :=
  twoElement (escapeIndex n).1 * cubicMatrix *
    (twoElement (escapeIndex n).1)⁻¹ * cubicMatrix⁻¹

theorem cubicCommutator_cube : ∀ n : Fin 15, (cubicCommutator n) ^ 3 = 1 := by
  intro n
  apply Subtype.ext
  revert n
  decide +kernel

theorem cubicCommutator_ne_one : ∀ n : Fin 15, cubicCommutator n ≠ 1 := by
  intro n h
  have hh := congrArg Subtype.val h
  have hn : ∀ n : Fin 15, (cubicCommutator n).val ≠ (1 : SL).val := by decide +kernel
  exact hn n hh

private theorem commutator_image (n : Fin 15) :
    element (escapeIndex n) * inner cubicMatrix *
        (element (escapeIndex n))⁻¹ * (inner cubicMatrix)⁻¹ = inner (cubicCommutator n) := by
  simp only [element, pair, escapeIndex, Bool.false_eq_true, ↓reduceIte, mul_one,
    cubicCommutator, map_mul, map_inv]

theorem escape_not_mem_core (n : Fin 15) (h : element (escapeIndex n) ∈ K) :
    (⟨element (escapeIndex n),h⟩ : K) ∉ pCore 2 K := by
  intro ha
  let a : K := ⟨element (escapeIndex n),h⟩
  let k : K := ⟨inner cubicMatrix,cubic_mem_local⟩
  let c : K := a * k * a⁻¹ * k⁻¹
  have hc : c ∈ pCore 2 K := by
    simpa only [c, mul_assoc] using (pCore 2 K).mul_mem ha
      ((pCore_normal (p := 2) (G := K)).conj_mem a⁻¹ ((pCore 2 K).inv_mem ha) k)
  have hc3 : c ^ 3 = 1 := by
    apply Subtype.ext
    change (element (escapeIndex n) * inner cubicMatrix *
      (element (escapeIndex n))⁻¹ * (inner cubicMatrix)⁻¹) ^ 3 = 1
    rw [commutator_image, ← map_pow, cubicCommutator_cube, map_one]
  have hc1 : c ≠ 1 := by
    intro hh
    have hh' := congrArg Subtype.val hh
    change element (escapeIndex n) * inner cubicMatrix *
      (element (escapeIndex n))⁻¹ * (inner cubicMatrix)⁻¹ = 1 at hh'
    rw [commutator_image, ← inner.map_one] at hh'
    exact cubicCommutator_ne_one n (inner_injective hh')
  have hd : orderOf c ∣ 8 := by
    simpa only [localSubgroup_twoCore_card] using (pCore 2 K).orderOf_dvd_natCard hc
  have hthree : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
  have hone : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 8 3) hd hthree
  exact hc1 (orderOf_eq_one_iff.mp hone)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.ActorCertificates
