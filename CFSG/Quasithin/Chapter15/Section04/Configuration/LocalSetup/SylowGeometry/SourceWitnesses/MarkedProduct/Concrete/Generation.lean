module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.Concrete

/-!
# Generating the marked symmetric-three product

The two permutation signs define a quotient of the actual plane-preserving
isometry group with kernel the independent rotations. A swapping isometry
exchanges the signs. Thus rotations and an element with different signs,
together with its swapped conjugate, generate the whole product.

Source: Aschbacher--Smith, the product quotient preceding 15.4.20,
combined manuscript of 1 March 2004, printed pp.1163--1164.
-/

@[expose] public section
open Subgroup
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct.Concrete
open FamilySource.ModuleStructure.BaumannPair

noncomputable def pairSign : base →* (ℤˣ × ℤˣ) where
  toFun g := (Equiv.Perm.sign (baseEquiv g).1, Equiv.Perm.sign (baseEquiv g).2)
  map_one' := by simp
  map_mul' a b := by simp

theorem code_mem_rotations (i j : LineCode) :
    codeMap (i,j,false) ∈ rotations ↔ i.2 = 0 ∧ j.2 = 0 := by
  constructor
  · intro h
    have hh := rotations_parity_zero _ h
    rwa [show codeEquiv.symm (codeMap (i,j,false)) = (i,j,false) from
      codeEquiv.symm_apply_apply _] at hh
  · rintro ⟨hi,hj⟩
    let r : RotationCode := Multiplicative.ofAdd ((i.1.val : ZMod 3), (j.1.val : ZMod 3))
    refine ⟨r, ?_⟩
    rw [rotationHom_code]
    congr 1
    apply Prod.ext
    · apply Prod.ext
      · apply Fin.ext
        exact ZMod.val_natCast_of_lt i.1.isLt
      · exact hi.symm
    · apply Prod.ext
      · apply Prod.ext
        · apply Fin.ext
          exact ZMod.val_natCast_of_lt j.1.isLt
        · exact hj.symm
      · rfl

theorem pairSign_eq_one_iff (g : base) : pairSign g = 1 ↔ g.val ∈ rotations := by
  obtain ⟨⟨i,j,b⟩, hg⟩ := codeMap_bijective.surjective g.val
  have hb : b = false := by
    have h := (base_iff g.val).mp g.property
    rwa [←hg, show codeEquiv.symm (codeMap (i,j,b)) = (i,j,b) from
      codeEquiv.symm_apply_apply _] at h
  subst b
  change (Equiv.Perm.sign (baseEquiv g).1, Equiv.Perm.sign (baseEquiv g).2) = _ ↔ _
  rw [baseEquiv_sign]
  rw [←hg, show codeEquiv.symm (codeMap (i,j,false)) = (i,j,false) from
    codeEquiv.symm_apply_apply _, code_mem_rotations]
  exact (show ∀ i j : Fin 2,
    ((if i = 0 then (1 : ℤˣ) else -1), (if j = 0 then (1 : ℤˣ) else -1)) = 1 ↔
      i = 0 ∧ j = 0 by decide +kernel) i.2 j.2

theorem swapping_conjugate_sign (g : base) (t : OrthogonalFourBinary.IsometryGroup)
    (ht : (codeEquiv.symm t).2.2 = true) :
    ∃ h : t * g.val * t⁻¹ ∈ base,
      pairSign ⟨t * g.val * t⁻¹,h⟩ = ((pairSign g).2, (pairSign g).1) := by
  obtain ⟨⟨i,j,b⟩, rfl⟩ := codeMap_bijective.surjective t
  rw [show codeEquiv.symm (codeMap (i,j,b)) = (i,j,b) from
    codeEquiv.symm_apply_apply _] at ht
  change b = true at ht
  subst b
  obtain ⟨p,rfl⟩ := productBase_surjective g
  let a := planeEquiv (planePermutation i)
  let b := planeEquiv (planePermutation j)
  let q : S3 × S3 := (a * p.2 * a⁻¹, b * p.1 * b⁻¹)
  have he : codeMap (i,j,true) * (productBase p).val * (codeMap (i,j,true))⁻¹ =
      productIsometry q := by
    apply mul_inv_eq_iff_eq_mul.mpr
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change candidate (i,j,true) ((productIsometry p).val v) =
      (productIsometry q).val (candidate (i,j,true) v)
    simp [candidate, productIsometry, q, a, b, LinearEquiv.mul_apply]
  refine ⟨he ▸ productIsometry_mem_base q, ?_⟩
  have hpair (r : S3 × S3) : pairSign (productBase r) =
      (Equiv.Perm.sign r.1, Equiv.Perm.sign r.2) := by
    change (Equiv.Perm.sign (baseEquiv (baseEquiv.symm r)).1,
      Equiv.Perm.sign (baseEquiv (baseEquiv.symm r)).2) = _
    rw [baseEquiv.apply_symm_apply]
  have he' : (⟨_,he ▸ productIsometry_mem_base q⟩ : base) = productBase q := Subtype.ext he
  rw [he',hpair,hpair]
  simp [q, mul_comm, mul_left_comm, mul_assoc]

theorem base_generated_of_independent_parity
    (D : Subgroup OrthogonalFourBinary.IsometryGroup) (hD : D ≤ base) (hrot : rotations ≤ D)
    (b t : OrthogonalFourBinary.IsometryGroup) (hb : b ∈ D)
    (hpar : (codeEquiv.symm b).1.2 ≠ (codeEquiv.symm b).2.1.2)
    (ht : (codeEquiv.symm t).2.2 = true) (hconj : t*b*t⁻¹ ∈ D) : D = base := by
  classical
  let b' : base := ⟨b,hD hb⟩
  let c' : base := ⟨t*b*t⁻¹,hD hconj⟩
  have hs : pairSign c' = ((pairSign b').2,(pairSign b').1) :=
    (swapping_conjugate_sign b' t ht).choose_spec
  have hne : (pairSign b').1 ≠ (pairSign b').2 := by
    have hh := baseEquiv_sign b'
    change pairSign b' = _ at hh
    rw [hh]
    exact (show ∀ a b : Fin 2, a ≠ b →
      (if a = 0 then (1 : ℤˣ) else -1) ≠ (if b = 0 then 1 else -1) by decide +kernel)
        _ _ hpar
  apply le_antisymm hD
  intro x hx
  let x' : base := ⟨x,hx⟩
  have hcases : pairSign x' = 1 ∨ pairSign x' = pairSign b' ∨
      pairSign x' = pairSign c' ∨ pairSign x' = pairSign (b'*c') := by
    rw [map_mul,hs]
    exact (show ∀ u v : ℤˣ × ℤˣ, u.1 ≠ u.2 →
      v = 1 ∨ v = u ∨ v = (u.2,u.1) ∨ v = u*(u.2,u.1) by decide +kernel)
      (pairSign b') (pairSign x') hne
  have hmem (d : base) (hd : d.val ∈ D) (he : pairSign x' = pairSign d) : x ∈ D := by
    have hquot : pairSign (x'*d⁻¹) = 1 := by rw [map_mul,map_inv,he,mul_inv_cancel]
    have hr : (x'*d⁻¹).val ∈ D := hrot ((pairSign_eq_one_iff _).mp hquot)
    simpa using D.mul_mem hr hd
  rcases hcases with h | h | h | h
  · exact hrot ((pairSign_eq_one_iff _).mp h)
  · exact hmem b' hb h
  · exact hmem c' hconj h
  · exact hmem (b'*c') (D.mul_mem hb hconj) h

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct.Concrete
