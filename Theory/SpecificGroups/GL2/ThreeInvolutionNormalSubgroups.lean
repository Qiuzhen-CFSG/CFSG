module
public import Theory.SpecificGroups.GL2.ThreeConjugacy
public import Mathlib.GroupTheory.Index

/-!
# Normal subgroups of GL₂(3) and its involutions

An odd normal subgroup is trivial, while a normal subgroup containing every
involution is the whole group. The checked eight-class table reduces both
claims to the displayed matrix representatives. Products of involutions
supply the unipotent and rotation; conjugate unipotents exclude odd normal
subgroups. These facts are used in the simplicity reduction for
Aschbacher–Smith I.4.2 (printed p.416).
-/

namespace Matrix.GeneralLinearGroup
open Subgroup
private abbrev G := GL (Fin 2) (ZMod 3)

/-- A normal subgroup of GL₂(3) with odd order is trivial. -/
public theorem three_odd_normal_eq_bot (N : Subgroup (GL (Fin 2) (ZMod 3))) [N.Normal]
    (ho : Odd (Nat.card N)) : N = ⊥ := by
  have hord : ∀ x ∈ N, Nat.Coprime 2 (orderOf x) := by
    intro x hx
    have hd : orderOf x ∣ Nat.card N := by
      rw [Subgroup.orderOf_coe (⟨x, hx⟩ : N)]
      exact orderOf_dvd_natCard (⟨x, hx⟩ : N)
    exact Nat.Coprime.of_dvd_right hd (Nat.prime_two.coprime_iff_not_dvd.mpr
      ho.not_two_dvd_nat)
  have hnot : threeUnipotent ∉ N := by
    intro hr
    have hr' := (inferInstance : N.Normal).conj_mem threeUnipotent hr threeRotation
    have hprod := N.pow_mem (N.mul_mem hr hr') 2
    have heq : (threeUnipotent *
        (threeRotation * threeUnipotent * threeRotation⁻¹)) ^ 2 = threeCentral := by
      decide +kernel
    rw [heq] at hprod
    have hbad := hord _ hprod
    have htwo : orderOf threeCentral = 2 := three_conjugacy_data.2.1 1
    rw [htwo] at hbad
    norm_num at hbad
  apply bot_unique
  intro x hx
  obtain ⟨i, hi, _⟩ := three_conjugacy_data.1 x
  obtain ⟨g, hg⟩ := isConj_iff.mp hi
  have hmem : threeClassRepr i ∈ N :=
    hg ▸ (inferInstance : N.Normal).conj_mem x hx g
  have hcop := hord _ hmem
  rw [three_conjugacy_data.2.1] at hcop
  fin_cases i <;> norm_num at hcop
  · change x = 1
    have hh : g * x * g⁻¹ = 1 := hg
    simpa [mul_assoc] using congrArg (fun y => g⁻¹ * y * g) hh
  · exact (hnot hmem).elim

/-- The involutions normally generate the actual GL₂(3) matrix group. -/
public theorem three_normal_eq_top_of_involutions (N : Subgroup (GL (Fin 2) (ZMod 3))) [N.Normal]
    (hN : ∀ x : GL (Fin 2) (ZMod 3), x ^ 2 = 1 → x ∈ N) : N = ⊤ := by
  let s : G := mkOfDetNeZero !![(0 : ZMod 3),1;1,0] (by decide)
  have hs : s ∈ N := hN s (by decide +kernel)
  have hb : threeReflection ∈ N := hN _ (by decide +kernel)
  have hrb : threeUnipotent * threeReflection ∈ N := hN _ (by decide +kernel)
  have hr : threeUnipotent ∈ N := by
    have he : threeUnipotent * threeReflection * threeReflection = threeUnipotent := by
      decide +kernel
    exact he ▸ N.mul_mem hrb hb
  have ha : threeRotation ∈ N := by
    have he : s * threeUnipotent = threeRotation := by decide +kernel
    exact he ▸ N.mul_mem hs hr
  have hz : threeCentral ∈ N := hN _ (by decide +kernel)
  have hall : ∀ i : Fin 8, threeClassRepr i ∈ N := by
    intro i
    fin_cases i
    · exact N.one_mem
    · exact hz
    · exact N.pow_mem ha 2
    · exact hr
    · exact N.mul_mem hr hz
    · exact hb
    · exact ha
    · exact N.inv_mem ha
  apply top_unique
  intro x _
  obtain ⟨i, hi, _⟩ := three_conjugacy_data.1 x
  obtain ⟨g, hg⟩ := isConj_iff.mp hi
  have hh := (inferInstance : N.Normal).conj_mem (threeClassRepr i) (hall i) g⁻¹
  simpa only [← hg, inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hh

end Matrix.GeneralLinearGroup
