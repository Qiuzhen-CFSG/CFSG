module

public import Mathlib.Data.Fin.VecNotation
public import Theory.Mathieu.M12.Centralizer2A.Representative
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Defs

public import Theory.Mathieu.M11.Properties.Centralizer
public import Theory.Mathieu.M11.Properties.InvolutionClasses
public import Theory.Mathieu.M12.Properties.InvolutionFusion
public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore.Order
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.Fusion
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.RepresentativeKernel.Enumeration
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.Quotient
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# Odd divisors of Mathieu involution centralizers

For every involution in each of the five literal Mathieu groups, its full
centralizer has order divisible by three, so is not a two-group. Native
involution fusion transports the centralizer orders 48, 192, 384, 2688 and
21504. The other M₁₂ and M₂₄ classes use explicit commuting cubic elements
in the original permutation carriers. Small kernel-checked permutation tables
certify those words before checking their order and commutation.

Only the one specified involution is used; there is no Sylow marking or
hypothesis about other involutions. These intrinsic facts supply the Mathieu
exclusions in the one-centralizer inspection of Aschbacher–Smith G.4.1,
printed p.342. The native fusion and centralizer results cite the corresponding
Mathieu entries of GLS3 Table 5.3 and Aschbacher–Smith 16.1.5.
-/

public section
open Subgroup
namespace Sporadic.Mathieu

private def cubic12Perm : Equiv.Perm (Fin 12) where
  toFun := ![1,9,4,8,11,7,3,10,6,0,5,2]
  invFun := ![9,0,11,6,2,10,8,5,3,1,7,4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private noncomputable def cubic12 : M12 :=
  let a : M12 := ⟨m12GeneratorA, m12GeneratorA_mem⟩
  let b : M12 := ⟨m12GeneratorB, m12GeneratorB_mem⟩
  (a * b * a * b * a * b * b) ^ 2

private theorem cubic12_coe : (cubic12 : Equiv.Perm (Fin 12)) = cubic12Perm := by
  change (m12GeneratorA * m12GeneratorB * m12GeneratorA * m12GeneratorB *
    m12GeneratorA * m12GeneratorB * m12GeneratorB) ^ 2 = _
  decide +kernel

private theorem cubic12_order : orderOf cubic12 = 3 := by
  rw [← orderOf_coe, cubic12_coe]
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

private theorem cubic12_mem : cubic12 ∈ centralizer ({m12Involution2A} : Set M12) := by
  apply mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  simp only [coe_mul, M12Centralizer2A.representative_coe, cubic12_coe]
  decide +kernel

private def word24Perm : Equiv.Perm (Fin 24) where
  toFun := ![5,3,13,16,18,8,12,9,10,6,1,20,4,15,0,7,22,14,19,2,11,23,17,21]
  invFun := ![14,10,19,1,12,0,9,15,5,7,8,20,6,2,17,13,3,22,4,18,11,23,16,21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def cubic24Perm : Equiv.Perm (Fin 24) where
  toFun := ![10,18,16,2,11,22,1,14,5,4,12,9,0,23,17,13,3,7,6,21,19,20,8,15]
  invFun := ![12,6,3,16,9,8,18,17,22,11,0,4,10,15,7,23,2,14,1,20,21,19,5,13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private noncomputable def word24 : M24 :=
  let a : M24 := ⟨m24GeneratorA, m24GeneratorA_mem⟩
  let b : M24 := ⟨m24GeneratorB, m24GeneratorB_mem⟩
  b * a * b⁻¹ * a * b * a * b⁻¹ * a * b * a * b

private theorem word24_coe : (word24 : Equiv.Perm (Fin 24)) = word24Perm := by
  change m24GeneratorB * m24GeneratorA * m24GeneratorB⁻¹ * m24GeneratorA *
    m24GeneratorB * m24GeneratorA * m24GeneratorB⁻¹ * m24GeneratorA *
    m24GeneratorB * m24GeneratorA * m24GeneratorB = _
  decide +kernel

private noncomputable def cubic24 : M24 :=
  let a : M24 := ⟨m24GeneratorA, m24GeneratorA_mem⟩
  word24⁻¹ * (a * word24 * a * word24⁻¹) ^ 2

private theorem cubic24_coe : (cubic24 : Equiv.Perm (Fin 24)) = cubic24Perm := by
  change (word24 : Equiv.Perm (Fin 24))⁻¹ *
    (m24GeneratorA * (word24 : Equiv.Perm (Fin 24)) * m24GeneratorA *
      (word24 : Equiv.Perm (Fin 24))⁻¹) ^ 2 = _
  rw [word24_coe]
  decide +kernel

private theorem cubic24_order : orderOf cubic24 = 3 := by
  rw [← orderOf_coe, cubic24_coe]
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

private theorem cubic24_mem : cubic24 ∈ M24InvolutionCentralizers.centralizer2B := by
  apply mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  simp only [coe_mul, cubic24_coe]
  change cubic24Perm * m24GeneratorA = m24GeneratorA * cubic24Perm
  decide +kernel


private theorem three_dvd_centralizer_of_cubic {G : Type*} [Group G] [Finite G]
    (z x : G) (hx : x ∈ centralizer ({z} : Set G)) (ho : orderOf x = 3) :
    3 ∣ Nat.card (centralizer ({z} : Set G)) := by
  let y : centralizer ({z} : Set G) := ⟨x, hx⟩
  have h : orderOf y = 3 := (orderOf_coe y).symm.trans ho
  simpa only [h] using orderOf_dvd_natCard y

private theorem not_isPGroup_two_of_three_dvd {G : Type*} [Group G] [Finite G]
    (h3 : 3 ∣ Nat.card G) : ¬ IsPGroup 2 G := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_card_dvd_pow
  have hd : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (h3.trans hn)
  norm_num at hd

/-- The full centralizer of every M₁₁ involution has order divisible by three. -/
theorem m11_involution_centralizer_three_dvd (i : M11) (hi : orderOf i = 2) :
    3 ∣ Nat.card (centralizer ({i} : Set M11)) := by
  rw [card_centralizer_eq_of_isConj _ _ (m11_involution_isConj_generatorA i hi)]
  change 3 ∣ Nat.card m11InvolutionCentralizer
  rw [m11_involutionCentralizer_card]
  decide

/-- Every involution in the actual M₁₁ carrier has a non-two-group centralizer. -/
theorem m11_involution_centralizer_not_isPGroup (i : M11) (hi : orderOf i = 2) :
    ¬ IsPGroup 2 (centralizer ({i} : Set M11)) :=
  not_isPGroup_two_of_three_dvd (m11_involution_centralizer_three_dvd i hi)

/-- Both native involution classes of M₁₂ have a cubic in their full centralizer. -/
theorem m12_involution_centralizer_three_dvd (i : M12) (hi : orderOf i = 2) :
    3 ∣ Nat.card (centralizer ({i} : Set M12)) := by
  rcases M12InvolutionFusion.involution_fusion i hi with h | h
  · rw [← card_centralizer_eq_of_isConj _ _ h]
    change 3 ∣ Nat.card M12SmallPair.firstParabolic
    rw [M12SmallPair.card_firstParabolic]
    decide
  · rw [← card_centralizer_eq_of_isConj _ _ h]
    exact three_dvd_centralizer_of_cubic _ cubic12 cubic12_mem cubic12_order

/-- Every involution in the actual M₁₂ carrier has a non-two-group centralizer. -/
theorem m12_involution_centralizer_not_isPGroup (i : M12) (hi : orderOf i = 2) :
    ¬ IsPGroup 2 (centralizer ({i} : Set M12)) :=
  not_isPGroup_two_of_three_dvd (m12_involution_centralizer_three_dvd i hi)

/-- The unique M₂₂ involution class has centralizer order divisible by three. -/
theorem m22_involution_centralizer_three_dvd (i : M22) (hi : orderOf i = 2) :
    3 ∣ Nat.card (centralizer ({i} : Set M22)) := by
  rw [card_centralizer_eq_of_isConj _ _ (m22_involutions_isConj i m22GeneratorAInM22
    hi M22RepresentativeKernel.representative_order)]
  change 3 ∣ Nat.card M22RepresentativeKernel.C
  rw [M22RepresentativeKernel.centralizer_card]
  decide

/-- Every involution in the actual M₂₂ carrier has a non-two-group centralizer. -/
theorem m22_involution_centralizer_not_isPGroup (i : M22) (hi : orderOf i = 2) :
    ¬ IsPGroup 2 (centralizer ({i} : Set M22)) :=
  not_isPGroup_two_of_three_dvd (m22_involution_centralizer_three_dvd i hi)

/-- The unique M₂₃ involution class has centralizer order divisible by three. -/
theorem m23_involution_centralizer_three_dvd (i : M23) (hi : orderOf i = 2) :
    3 ∣ Nat.card (centralizer ({i} : Set M23)) := by
  rw [card_centralizer_eq_of_isConj _ _ (M23Geometry.involutions_isConj i
    M23Geometry.involutionRepresentative hi M23Geometry.involutionRepresentative_order),
    M23Geometry.involutionRepresentative_centralizer_card]
  decide

/-- Every involution in the actual M₂₃ carrier has a non-two-group centralizer. -/
theorem m23_involution_centralizer_not_isPGroup (i : M23) (hi : orderOf i = 2) :
    ¬ IsPGroup 2 (centralizer ({i} : Set M23)) :=
  not_isPGroup_two_of_three_dvd (m23_involution_centralizer_three_dvd i hi)

/-- Both native involution classes of M₂₄ have a cubic in their full centralizer. -/
theorem m24_involution_centralizer_three_dvd (i : M24) (hi : orderOf i = 2) :
    3 ∣ Nat.card (centralizer ({i} : Set M24)) := by
  rcases M24InvolutionCentralizers.involution_classes i hi with h | h
  · rw [← card_centralizer_eq_of_isConj _ _ h]
    change 3 ∣ Nat.card M24InvolutionCentralizers.centralizer2A
    rw [M24InvolutionCentralizers.TwoA.centralizer_card]
    decide
  · rw [← card_centralizer_eq_of_isConj _ _ h]
    exact three_dvd_centralizer_of_cubic _ cubic24 cubic24_mem cubic24_order

/-- Every involution in the actual M₂₄ carrier has a non-two-group centralizer. -/
theorem m24_involution_centralizer_not_isPGroup (i : M24) (hi : orderOf i = 2) :
    ¬ IsPGroup 2 (centralizer ({i} : Set M24)) :=
  not_isPGroup_two_of_three_dvd (m24_involution_centralizer_three_dvd i hi)

end Sporadic.Mathieu
