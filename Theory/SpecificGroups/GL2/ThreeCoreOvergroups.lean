module

public import Theory.SpecificGroups.GL2.ThreeResidualImages.QuaternionCore
public import Mathlib.GroupTheory.Sylow

/-!
# Two-subgroups above the quaternion core of GL2(3)

The actual two-core is Q8 and every Sylow two-subgroup has order sixteen.
Consequently any subgroup between the core and a fixed Sylow subgroup is
one of the two endpoints. The transported version retains an arbitrary
actual GL2(3) isomorphism and the original subgroups.

Source: Aschbacher--Smith 2.5.3(4), printed p.553, the small-component
contained-normalizer branch after O2(M∩D)≤D∩O2(H_U).
-/

public section
namespace Matrix.GeneralLinearGroup
open Subgroup
local notation "K" => GL (Fin 2) (ZMod 3)

/-- The intrinsic two-core is the concrete quaternion subgroup. -/
theorem three_twoCore_eq_quaternion : pCore 2 K = threeQuaternion := by
  exact (pCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K)).symm.trans
    (three_twoCore_image ⊤ le_top)

/-- The interval from the quaternion core to a Sylow subgroup has two members. -/
theorem three_subgroup_eq_core_or_sylow
    (P : Sylow 2 K) (R : Subgroup K)
    (hQR : pCore 2 K ≤ R) (hRP : R ≤ P) :
    R = pCore 2 K ∨ R = (P : Subgroup K) := by
  have hQcard : Nat.card (pCore 2 K) = 8 := by
    rw [three_twoCore_eq_quaternion, threeQuaternion_card]
  have hPcard : Nat.card P = 16 := by
    rw [P.card_eq_multiplicity, Matrix.card_GL_field]
    norm_num [Fin.prod_univ_two]
    decide +kernel
  have hge : 8 ≤ Nat.card R := by
    rw [← hQcard]
    exact Nat.card_le_card_of_injective (inclusion hQR) (inclusion_injective hQR)
  have hd : Nat.card R ∣ 16 := hPcard ▸ card_dvd_of_le hRP
  obtain ⟨a, ha⟩ := hd
  have ha2 : a ≤ 2 := by nlinarith
  have he : Nat.card R = 8 ∨ Nat.card R = 16 := by
    interval_cases a <;> omega
  rcases he with he | he
  · exact Or.inl (eq_of_le_of_card_ge hQR (by omega)).symm
  · exact Or.inr (eq_of_le_of_card_ge hRP (by omega))

/-- The same two alternatives under a specified actual GL2(3) isomorphism. -/
theorem subgroup_eq_core_or_sylow_of_equiv_three
    {A : Type*} [Group A] (e : A ≃* K) (P : Sylow 2 A) (R : Subgroup A)
    (hQR : pCore 2 A ≤ R) (hRP : R ≤ P) :
    R = pCore 2 A ∨ R = (P : Subgroup A) := by
  let : Finite A := Finite.of_injective e e.injective
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : (pCore 2 A).map e.toMonoidHom = pCore 2 K := pCore_map_iso 2 e
  have hQ : pCore 2 K ≤ R.map e.toMonoidHom := hmap ▸ map_mono hQR
  rcases three_subgroup_eq_core_or_sylow P' (R.map e.toMonoidHom) hQ
      (map_mono hRP) with he | he
  · exact Or.inl (Subgroup.map_injective (f := e.toMonoidHom) e.injective (he.trans hmap.symm))
  · exact Or.inr (Subgroup.map_injective (f := e.toMonoidHom) e.injective he)

end Matrix.GeneralLinearGroup
