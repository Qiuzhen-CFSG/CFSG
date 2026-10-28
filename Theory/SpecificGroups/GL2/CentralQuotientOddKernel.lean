module
public import Theory.SpecificGroups.GL2.CentralQuotientCenter
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Index

/-!
# Odd central kernels detected by quotient involutions

Let F be a finite field of cardinality congruent to three modulo four, and
let Z be a central subgroup of GL₂(F). If the quotient by Z has a central
element of order two, then Z has odd order. The quotient uses the caller's
normality instance throughout; no oddness or center-lifting assumption is added.

The cardinality congruence excludes characteristic two. The center-lifting
theorem for GL₂, proved using the nonzero trace of elementary transvections,
puts the given involution in the image of the original scalar center. Restrict
the quotient homomorphism to that center: its kernel has cardinality |Z| and
its range has even cardinality. The scalar embedding identifies the center's
cardinality with |F| − 1. The kernel-range cardinality formula then excludes
even |Z|, since |F| − 1 is not divisible by four. This includes the field F₃.

Source: Brauer, *On finite Desarguesian planes. II*, §2, p125,
(2.1)--(2.4), describing the quotient center as the scalar image. This module
supplies the odd-kernel input for transferring full-GL₂ Sylow subgroups to
central quotients without importing any classification campaign.
-/

namespace Matrix.GeneralLinearGroup

public theorem odd_card_of_central_quotient_involution
    {F : Type*} [Field F] [Finite F]
    (hcard : Nat.card F % 4 = 3)
    (Z : Subgroup (GL (Fin 2) F)) [Z.Normal]
    (hZ : Z ≤ Subgroup.center (GL (Fin 2) F))
    (z : GL (Fin 2) F ⧸ Z)
    (hz : z ∈ Subgroup.center (GL (Fin 2) F ⧸ Z))
    (hzorder : orderOf z = 2) : Odd (Nat.card Z) := by
  let := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro heq
    have heven := FiniteField.even_card_of_char_two heq
    rw [← Nat.card_eq_fintype_card] at heven
    omega
  let C := Subgroup.center (GL (Fin 2) F)
  let projection : C →* GL (Fin 2) F ⧸ Z := (QuotientGroup.mk' Z).comp C.subtype
  have hker : projection.ker = Z.subgroupOf C := by
    ext A
    simp [projection, MonoidHom.mem_ker, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  have hkerCard : Nat.card projection.ker = Nat.card Z := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ).toEquiv
  have hzrange : z ∈ projection.range := by
    obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective Z z
    exact ⟨⟨A, mem_center_of_quotient_mem_center (Ring.two_ne_zero hchar) Z hZ A hz⟩, rfl⟩
  have hrange : 2 ∣ Nat.card projection.range := by
    have h := projection.range.orderOf_dvd_natCard hzrange
    rwa [hzorder] at h
  have hinj : Function.Injective (scalar (Fin 2) : Fˣ →* GL (Fin 2) F) := by
    intro a b hab
    apply Units.ext
    have h := congrArg (fun A : GL (Fin 2) F => A.val 0 0) hab
    simpa [coe_scalar, Matrix.scalar_apply] using h
  have hcenterCard : Nat.card C = Nat.card F - 1 := by
    change Nat.card (Subgroup.center (GL (Fin 2) F)) = _
    rw [center_eq_range_scalar]
    exact (Nat.card_congr (Equiv.ofInjective (scalar (Fin 2)) hinj)).symm.trans
      (Nat.card_units F)
  have hproduct : Nat.card Z * Nat.card projection.range = Nat.card F - 1 := by
    have h := projection.ker.card_mul_index
    rw [Subgroup.index_ker, hkerCard, hcenterCard] at h
    exact h
  rw [Nat.odd_iff]
  by_contra hnot
  have heven : 2 ∣ Nat.card Z := by omega
  have hfour : 4 ∣ Nat.card F - 1 := by
    rw [← hproduct]
    exact mul_dvd_mul heven hrange
  omega

end Matrix.GeneralLinearGroup
