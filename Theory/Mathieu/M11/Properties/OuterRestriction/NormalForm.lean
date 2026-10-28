module

public import Theory.Mathieu.M11.Properties.Order

/-!
# Schreier coordinates for the M11 automorphism calculation

The four existing Schreier transversals give 11 · 10 · 9 · 8 distinct
elements of the concrete Witt-design group. Its proved order shows that
these coordinates cover the group. They supply a bounded domain for the
finite generator-image calculation of Out(M11) in GLS3, Table 5.3a.
-/

namespace Sporadic.Mathieu.M11Outer
open Theory.GroupTheory M11OrderCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Indices for the existing four Schreier transversals. -/
public abbrev Index := Fin 11 × Fin 10 × Fin 9 × Fin 8

/-- The permutation with the indicated Schreier coordinates. -/
@[expose] public def perm (p : Index) : Equiv.Perm (Fin 11) :=
  m11L0Rep p.1 * (m11L1Rep p.2.1 * (m11L2Rep p.2.2.1 * m11L3Rep p.2.2.2))

private theorem word_mem {n : ℕ} (g : Fin n → Equiv.Perm (Fin 11))
    (hg : ∀ i, g i ∈ M11) (w : List (Fin n)) : evalWord g w ∈ M11 := by
  induction w with
  | nil => exact M11.one_mem
  | cons i w ih => exact M11.mul_mem (hg i) ih

private theorem gen0_mem (i : Fin 4) : m11L0Gen i ∈ M11 := by
  fin_cases i
  · change m11L0G0 ∈ M11
    rw [← m11GeneratorA_eq_m11L0G0]
    exact m11GeneratorA_mem
  · change m11L0G1 ∈ M11
    rw [← m11GeneratorB_eq_m11L0G1]
    exact m11GeneratorB_mem
  · exact M11.inv_mem (m11GeneratorA_eq_m11L0G0 ▸ m11GeneratorA_mem)
  · exact M11.inv_mem (m11GeneratorB_eq_m11L0G1 ▸ m11GeneratorB_mem)

private theorem gen1_mem (i : Fin 4) : m11L1Gen i ∈ M11 := by
  rw [m11L1Gen_eq_word]
  exact word_mem _ gen0_mem _

private theorem gen2_mem (i : Fin 6) : m11L2Gen i ∈ M11 := by
  rw [m11L2Gen_eq_word]
  exact word_mem _ gen1_mem _

private theorem gen3_mem (i : Fin 6) : m11L3Gen i ∈ M11 := by
  rw [m11L3Gen_eq_word]
  exact word_mem _ gen2_mem _

/-- Each coordinate permutation preserves the Witt design. -/
public theorem perm_mem (p : Index) : perm p ∈ M11 := by
  apply M11.mul_mem
  · rw [m11L0Rep_eq_word]
    exact word_mem _ gen0_mem _
  · apply M11.mul_mem
    · rw [m11L1Rep_eq_word]
      exact word_mem _ gen1_mem _
    · apply M11.mul_mem
      · rw [m11L2Rep_eq_word]
        exact word_mem _ gen2_mem _
      · rw [m11L3Rep_eq_word]
        exact word_mem _ gen3_mem _

/-- The Schreier-coordinate element of the actual M11 carrier. -/
@[expose] public noncomputable def element (p : Index) : M11 := ⟨perm p, perm_mem p⟩

private theorem rep1_fix : ∀ i : Fin 10, m11L1Rep i 1 = 1 := by decide +kernel
private theorem rep2_fix1 : ∀ i : Fin 9, m11L2Rep i 1 = 1 := by decide +kernel
private theorem rep2_fix2 : ∀ i : Fin 9, m11L2Rep i 2 = 2 := by decide +kernel
private theorem rep3_fix1 : ∀ i : Fin 8, m11L3Rep i 1 = 1 := by decide +kernel
private theorem rep3_fix2 : ∀ i : Fin 8, m11L3Rep i 2 = 2 := by decide +kernel
private theorem rep3_fix3 : ∀ i : Fin 8, m11L3Rep i 3 = 3 := by decide +kernel

private theorem perm_injective : Function.Injective perm := by
  rintro ⟨i,j,k,l⟩ ⟨i',j',k',l'⟩ h
  have hi : i = i' := by
    apply m11L0Point_injective
    have hh := Equiv.congr_fun h 1
    simpa only [perm, Equiv.Perm.mul_apply, rep3_fix1, rep2_fix1,
      rep1_fix, m11L0RepPoint] using hh
  subst i'
  have h1 := mul_left_cancel h
  have hj : j = j' := by
    apply m11L1Point_injective
    have hh := Equiv.congr_fun h1 2
    simpa only [Equiv.Perm.mul_apply, rep3_fix2, rep2_fix2,
      m11L1RepPoint] using hh
  subst j'
  have h2 := mul_left_cancel h1
  have hk : k = k' := by
    apply m11L2Point_injective
    have hh := Equiv.congr_fun h2 3
    simpa only [Equiv.Perm.mul_apply, rep3_fix3, m11L2RepPoint] using hh
  subst k'
  have h3 := mul_left_cancel h2
  have hl : l = l' := by
    apply m11L3Point_injective
    simpa only [m11L3RepPoint] using Equiv.congr_fun h3 4
  subst l'
  rfl

/-- Every design automorphism has one of the 7920 Schreier coordinates. -/
public theorem element_surjective : Function.Surjective element := by
  apply (Nat.bijective_iff_injective_and_card element).mpr ?_ |>.surjective
  constructor
  · intro p q h
    exact perm_injective (congrArg Subtype.val h)
  · rw [m11_order]
    simp [Index]

end Sporadic.Mathieu.M11Outer
