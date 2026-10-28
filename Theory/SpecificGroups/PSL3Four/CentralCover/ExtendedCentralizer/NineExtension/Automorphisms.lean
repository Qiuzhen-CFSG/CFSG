module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Module.ZMod
public import Theory.SpecificGroups.GL2.ThreeConjugacy

/-!
# Automorphisms of the elementary group of order nine

The additive-linear correspondence identifies Aut(E₉) with the actual matrix
group GL₂(3). Its order is 48. Every odd normal subgroup is trivial: the
conjugacy table leaves only the identity and unipotent classes, while two
conjugate unipotents generate an element whose square is the scalar involution.

These intrinsic automorphism facts support the finite-extension argument used
in Aschbacher–Smith, *The Classification of Quasithin Groups*, 15.3.38,
printed p.1137. The conjugacy computations are kernel-checked in `ThreeConjugacy`.
-/

namespace Matrix.PSL3Four.ExtendedCentralizer.NineExtension

open Matrix
local notation "E₉" => Multiplicative (Fin 2 → ZMod 3)
/-- The additive-linear correspondence for the concrete elementary group of order nine. -/
public noncomputable def automorphismEquiv : MulAut E₉ ≃* GL (Fin 2) (ZMod 3) := by
  let autLinear : MulAut E₉ ≃* ((Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3)) :=
    { toFun := fun aut =>
        { AddEquiv.toMultiplicative.symm aut with
          map_smul' := ZMod.map_smul (AddEquiv.toMultiplicative.symm aut) }
      invFun := fun aut => AddEquiv.toMultiplicative aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  exact autLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Fin 2 → ZMod 3)).symm.trans
      (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun (ZMod 3) (Fin 2))).symm)

private theorem matrix_card : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  rw [Matrix.card_GL_field]
  norm_num [Fin.prod_univ_two]

open Matrix.GeneralLinearGroup Subgroup
private theorem matrix_odd_normal_eq_bot (N : Subgroup (GL (Fin 2) (ZMod 3))) [N.Normal]
    (hc : Nat.Coprime 2 (Nat.card N)) : N = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨i, hi, -⟩ := three_conjugacy_data.1 x
  obtain ⟨g, hg⟩ := isConj_iff.mp hi
  have ho := (MulAut.conj g).orderOf_eq x
  rw [show MulAut.conj g x = threeClassRepr i from hg,
    three_conjugacy_data.2.1] at ho
  have hcop : Nat.Coprime 2 (orderOf x) :=
    hc.of_dvd_right (N.orderOf_dvd_natCard hx)
  have hi03 : i = 0 ∨ i = 3 := by
    have ht : ∀ j : Fin 8, Nat.Coprime 2 (![1,2,4,3,6,2,8,8] j) →
        j = 0 ∨ j = 3 := by decide
    exact ht i (by rwa [ho])
  rcases hi03 with rfl | rfl
  · exact mem_bot.mpr (orderOf_eq_one_iff.mp (by simpa using ho.symm))
  · have hu : threeUnipotent ∈ N := by
      have hm := (inferInstance : N.Normal).conj_mem x hx g
      rw [hg] at hm
      simpa [threeClassRepr] using hm
    have hl := (inferInstance : N.Normal).conj_mem _ hu threeRotation
    have hid : (threeUnipotent *
        (threeRotation * threeUnipotent * threeRotation⁻¹)) ^ 2 = threeCentral := by
      decide +kernel
    have hz : threeCentral ∈ N := hid ▸ N.pow_mem (N.mul_mem hu hl) 2
    have hoz : orderOf threeCentral = 2 := by
      simpa [threeClassRepr] using three_conjugacy_data.2.1 (1 : Fin 8)
    have hn := hc.of_dvd_right (N.orderOf_dvd_natCard hz)
    norm_num [hoz] at hn

/-- The full automorphism group of the elementary group of order nine has order 48. -/
public theorem automorphism_card {R : Type*} [Group R]
    (e : R ≃* E₉) : Nat.card (MulAut R) = 48 := by
  exact (Nat.card_congr ((MulAut.congr e).trans automorphismEquiv).toEquiv).trans matrix_card

/-- An odd normal subgroup of the full automorphism group of E₉ is trivial. -/
public theorem odd_normal_eq_bot {R : Type*} [Group R]
    (e : R ≃* E₉) (N : Subgroup (MulAut R)) [N.Normal]
    (hc : Nat.Coprime 2 (Nat.card N)) : N = ⊥ := by
  let f := (MulAut.congr e).trans automorphismEquiv
  have : (N.map f.toMonoidHom).Normal :=
    (inferInstance : N.Normal).map _ f.surjective
  have hm := matrix_odd_normal_eq_bot (N.map f.toMonoidHom) (by
    rwa [Subgroup.card_map_of_injective f.injective])
  exact (Subgroup.map_eq_bot_iff_of_injective N f.injective).mp hm

end Matrix.PSL3Four.ExtendedCentralizer.NineExtension
