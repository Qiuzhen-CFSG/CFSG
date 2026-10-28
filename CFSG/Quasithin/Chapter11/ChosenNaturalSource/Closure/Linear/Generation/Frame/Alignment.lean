module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame.Hall
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
open Subgroup Subgroup.OddHall Matrix
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.CartanActions.BorelQuotient
open scoped MatrixGroups
@[expose] public noncomputable section
/-!
# Full SL₃ Sylow and Cartan alignment

Sylow conjugacy aligns the upper unipotent group and its Borel normalizer.
Hall conjugacy inside that solvable Borel then aligns the actual Cartan image
with the full determinant-one diagonal torus, preserving the Sylow.
The cubic scalar center is retained, also over the field of four elements.
Source: Aschbacher–Smith 11.5.7, printed p.781.
-/

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame

private theorem hall_map {A B : Type*} [Group A] [Group B] [Finite A]
    {X : Subgroup A} (hX : IsHallSubgroup oddPrimes X)
    (f : A →* B) (hf : Function.Surjective f) :
    IsHallSubgroup oddPrimes (X.map f) :=
  ⟨fun p hp => hX.p_in_pi_of_p_dvd_card p (hp.trans (X.card_map_dvd f)),
   fun p hp => hX.p_in_pi_of_p_dvd_index p (hp.trans (X.index_map_dvd hf))⟩

variable {F : Type*} [Field F] [Finite F]

theorem torusSL_hall {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    IsHallSubgroup oddPrimes ((torusSL F).range.subgroupOf (borelSL F)) := by
  constructor
  · intro p hp hp2
    have ho : Odd (Nat.card ((torusSL F).range.subgroupOf (borelSL F))) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe (torusSL_le_borel F)).toEquiv,
        ← Nat.card_congr (torusSLEquiv F).toEquiv, Nat.card_prod]
      exact (units_odd F hF).mul (units_odd F hF)
    exact ho.not_two_dvd_nat (hp2 ▸ hp)
  · intro p hp hp2
    rw [(borelSL_complement F).index_eq_card,
      Nat.card_congr (subgroupOfEquivOfLe (unipotentSL_le_borelSL F)).toEquiv,
      card_unipotentSL, hF, ← pow_mul] at hp
    exact hp2 (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two hp)

theorem borelSL_solvable {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Group.IsSolvable (borelSL F) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := (pCore_isPGroup (p := 2) (G := borelSL F)).isNilpotent
  let e := quotientSLTorusEquiv F hF
  let : Group.IsSolvable (borelSL F ⧸ pCore 2 (borelSL F)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 (borelSL F))).mpr
    ⟨inferInstance, inferInstance⟩

/-- Simultaneously align the given Sylow and its actual odd Hall subgroup in full SL₃. -/
theorem exists_sylow_cartan_alignment {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 SL(3,F)) (C : Subgroup SL(3,F))
    (hCN : C ≤ normalizer (S : Set SL(3,F)))
    (hHall : IsHallSubgroup oddPrimes (C.subgroupOf (normalizer (S : Set SL(3,F))))) :
    ∃ g : SL(3,F),
      (unipotentSL F).map (MulAut.conj g).toMonoidHom = (S : Subgroup SL(3,F)) ∧
      (torusSL F).range.map (MulAut.conj g).toMonoidHom = C := by
  obtain ⟨a, haS, haN⟩ := sylowSL_normalizer_conjugate F hn hF S
  let N := normalizer (S : Set SL(3,F))
  let e : borelSL F ≃* N :=
    ((borelSL F).equivMapOfInjective (MulAut.conj a).toMonoidHom
      (MulAut.conj a).injective).trans (MulEquiv.subgroupCongr haN)
  have he (x : borelSL F) : (e x : SL(3,F)) = a * x * a⁻¹ := rfl
  let H := (C.subgroupOf N).map e.symm.toMonoidHom
  have hH : IsHallSubgroup oddPrimes H := hall_map hHall _ e.symm.surjective
  obtain ⟨b, hb⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable
    (borelSL_solvable hF) (torusSL_hall hF) hH
  have hC : H.map (N.subtype.comp e.toMonoidHom) = C := by
    change ((C.subgroupOf N).map e.symm.toMonoidHom).map _ = C
    rw [Subgroup.map_map]
    have heq : (N.subtype.comp e.toMonoidHom).comp e.symm.toMonoidHom = N.subtype := by
      ext x : 1
      exact congrArg Subtype.val (e.apply_symm_apply x)
    rw [heq, map_subgroupOf_eq_of_le hCN]
  refine ⟨a * (b : SL(3,F)), ?_, ?_⟩
  · have hbU : (unipotentSL F).map (MulAut.conj (b : SL(3,F))).toMonoidHom =
        unipotentSL F := mem_normalizer_iff_map_conj_eq.mp
          ((normalizer_unipotentSL F).symm ▸ b.property)
    calc
      _ = ((unipotentSL F).map (MulAut.conj (b : SL(3,F))).toMonoidHom).map
          (MulAut.conj a).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext x : 1
        simp [MulAut.conj_apply, mul_assoc]
      _ = _ := by rw [hbU, haS]
  · rw [hb] at hC
    rw [Subgroup.map_map] at hC
    have heq : (N.subtype.comp e.toMonoidHom).comp (MulAut.conj b).toMonoidHom =
        (MulAut.conj (a * (b : SL(3,F)))).toMonoidHom.comp (borelSL F).subtype := by
      ext x : 1
      change a * ((b : SL(3,F)) * x * (b : SL(3,F))⁻¹) * a⁻¹ = _
      simp [MulAut.conj_apply, mul_assoc]
    rw [heq, ← Subgroup.map_map, map_subgroupOf_eq_of_le (torusSL_le_borel F)] at hC
    exact hC
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame
