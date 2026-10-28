module

public import Theory.GroupTheory.PGroup.BinaryModular
public import Theory.GroupTheory.PGroup.SymplecticType
public import Theory.GroupTheory.PGroup.CentralProductOmegaCenter

/-!
# Ambient reductions for Hall's modular case

In the central-product core used in Hall's theorem, the intersection of the
extraspecial factor with any subgroup of the residual factor has exponent
dividing two. Also the centralizer of the squares of the characteristic cyclic
subgroup is characteristic in the ambient group. These facts are precisely
the ambient inputs to the center-of-omega argument.

Source: Gorenstein, *Finite Groups*, Section 5.4, proof of Theorem 4.9.
-/

open Subgroup

/-- Intersections with the residual factor lie in the extraspecial center,
which has order two. The trivial extraspecial factor is allowed. -/
public theorem BinaryHallCore.intersection_pow_two_eq_one
    {P : Type*} [Group P] {E D Z : Subgroup P} (h : BinaryHallCore E D Z)
    (M : Subgroup P) (hMD : M ≤ D) : ∀ x ∈ E ⊓ M, x ^ 2 = 1 := by
  intro x hx
  rcases h.extraspecial_or_bot with hE | hE
  · have hx1 : x = 1 := by simpa [hE] using hx.1
    simp [hx1]
  · let : IsExtraspecial 2 E := hE
    have hxC : (⟨x, hx.1⟩ : E) ∈ center E := by
      apply mem_center_iff.mpr
      intro e
      exact Subtype.ext (h.centralizes (hMD hx.2) e e.property)
    have hp := pow_card_eq_one' (x := (⟨⟨x, hx.1⟩, hxC⟩ : center E))
    rw [IsExtraspecial.center_order_p 2 E] at hp
    exact congrArg (fun z : center E => ((z : E) : P)) hp

/-- The centralizer `EM` of the squares of the specified cyclic subgroup is
characteristic in the full ambient group of a Hall core. -/
public theorem BinaryHallCore.characteristic_modular_overgroup
    {P : Type*} [Group P] {E D Z : Subgroup P} (h : BinaryHallCore E D Z)
    (a : P) (ha : Z = zpowers a) :
    (E ⊔ (D ⊓ centralizer (zpowers (a ^ 2) : Set P))).Characteristic := by
  let : (zpowers a).Characteristic := ha ▸ h.characteristic
  apply characteristic_sup_inf_centralizer_zpowers_sq E D a
    (h.le_tail (ha ▸ mem_zpowers a)) h.sup_eq_top h.centralizes

/-- The modular omega calculation supplies a noncyclic characteristic abelian
subgroup of the original Hall core's ambient group. In particular, this does
not require the residual factor itself to be characteristic. -/
public theorem BinaryHallCore.exists_noncyclic_characteristic_abelian_of_modular_omega
    {P : Type*} [Group P] {E D Z : Subgroup P} (h : BinaryHallCore E D Z)
    (a : P) (ha : Z = zpowers a)
    [IsMulCommutative (omega ↥(D ⊓ centralizer (zpowers (a ^ 2) : Set P)) (p := 2) 2)]
    (hncyc : ¬ IsCyclic (omega₁ ↥(D ⊓ centralizer (zpowers (a ^ 2) : Set P)) (p := 2))) :
    ∃ A : Subgroup P, A.Characteristic ∧ IsMulCommutative A ∧ ¬ IsCyclic A := by
  let M := D ⊓ centralizer (zpowers (a ^ 2) : Set P)
  let : (E ⊔ M).Characteristic := h.characteristic_modular_overgroup a ha
  exact exists_noncyclic_characteristic_abelian_of_characteristic_product_omega E M
    (inf_le_left.trans h.centralizes) (h.intersection_pow_two_eq_one M inf_le_left) hncyc
