module

public import Theory.SpecificGroups.GL2.FiniteQuadraticTorus
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A quadratic norm-one torus in SL₂ over a field of characteristic two

The actual quadratic extension has a cyclic norm-one subgroup of order q+1.
Its regular representation and its Frobenius reflection have determinant one:
the relevant determinant orders divide, respectively, both q+1 and q−1,
or both 2 and q−1. Frobenius inverts the norm-one subgroup.

This extracts the rank-one part of the proof in
`SymplecticFour.CentralCovers.OddPrimary.Nonsplit`, using the established
`GL2.FiniteQuadraticTorus` regular representation. No symplectic embedding is
used here. `QuadraticTorus` embeds the resulting matrices in the octonion G₂
model for Aschbacher–Smith I.1.3–I.1.4 and GLS3 §6.1.
-/

@[expose] public section

open Matrix Subgroup
namespace Atlas.G2.MultiplierOrdinary.Nondefining.QuadraticTorus
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local notation "SL" => SpecialLinearGroup (Fin 2) F

noncomputable abbrev normOne (F : Type*) [Field F] [Finite F] [CharP F 2] :=
  rootsOfUnity (Nat.card F + 1) (FiniteField.Extension F 2 2)

theorem card_normOne : Nat.card (normOne F) = Nat.card F + 1 := by
  change Nat.card (rootsOfUnity (Nat.card F + 1) (FiniteField.Extension F 2 2)) = _
  rw [rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker, Nat.card_units,
    FiniteField.natCard_extension]
  apply Nat.gcd_eq_right
  rw [show (Nat.card F)^2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) by
    simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1]
  exact dvd_mul_left _ _

theorem exists_normOne_SL :
    ∃ (s : normOne F →* SL) (v : SL),
      Function.Injective s ∧ ∀ c, v * s c * v⁻¹ = s c⁻¹ := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let E := FiniteField.Extension F 2 2
  let C := rootsOfUnity (Nat.card F + 1) E
  have hcard : Nat.card C = Nat.card F + 1 := card_normOne
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have heven : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq F 2))
  have hodd : Odd (Nat.card F - 1) := Nat.Even.sub_odd hq heven (by decide)
  have hcop : Nat.Coprime (Nat.card F + 1) (Nat.card F - 1) := by
    rw [show Nat.card F + 1 = (Nat.card F - 1) + 2 by omega,
      Nat.coprime_self_add_left]
    exact hodd.coprime_two_left
  obtain ⟨ρ, w, hi, hw, _, hconj, _⟩ := GeneralLinearGroup.exists_finite_quadratic_torus F 2
  let r : C →* GL (Fin 2) F := ρ.comp C.subtype
  have hd (c : C) : GeneralLinearGroup.det (r c) = 1 := by
    apply orderOf_eq_one_iff.mp
    have hd1 : orderOf (GeneralLinearGroup.det (r c)) ∣ Nat.card F + 1 := by
      rw [← hcard]
      exact (orderOf_map_dvd (GeneralLinearGroup.det.comp r) c).trans (orderOf_dvd_natCard c)
    have hd2 : orderOf (GeneralLinearGroup.det (r c)) ∣ Nat.card F - 1 := by
      simpa only [Nat.card_units] using orderOf_dvd_natCard (GeneralLinearGroup.det (r c))
    exact Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  have hwd : GeneralLinearGroup.det w = 1 := by
    apply orderOf_eq_one_iff.mp
    have h2 : (GeneralLinearGroup.det w)^2 = 1 := by rw [← map_pow, hw, map_one]
    have hq : orderOf (GeneralLinearGroup.det w) ∣ Nat.card F - 1 := by
      simpa only [Nat.card_units] using orderOf_dvd_natCard (GeneralLinearGroup.det w)
    exact Nat.eq_one_of_dvd_coprimes hodd.coprime_two_left (orderOf_dvd_of_pow_eq_one h2) hq
  let s : C →* SL := {
    toFun c := ⟨(r c).val, congrArg Units.val (hd c)⟩
    map_one' := Subtype.ext (congrArg Units.val r.map_one)
    map_mul' c d := Subtype.ext (congrArg Units.val (r.map_mul c d)) }
  let v : SL := ⟨w.val, congrArg Units.val hwd⟩
  have hs : Function.Injective s := by
    intro c d h
    apply Subtype.ext
    exact hi (Units.ext (congrArg Subtype.val h))
  have hv (c : C) : v * s c * v⁻¹ = s c⁻¹ := by
    apply SpecialLinearGroup.toGL_injective
    have hvGL : SpecialLinearGroup.toGL v = w := Units.ext rfl
    have hsGL (d : C) : SpecialLinearGroup.toGL (s d) = r d := Units.ext rfl
    simp only [map_mul, map_inv, hvGL, hsGL]
    change w * ρ c.val * w⁻¹ = (ρ c.val)⁻¹
    rw [hconj, ← map_inv]
    apply congrArg ρ
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact (mem_rootsOfUnity _ _).mp c.property
  exact ⟨s, v, hs, hv⟩

end Atlas.G2.MultiplierOrdinary.Nondefining.QuadraticTorus

end
