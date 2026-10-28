module

public import Theory.SpecificGroups.ReeTwo.ParabolicIndexTwo.Derived
public import Theory.SpecificGroups.ReeTwo.ParabolicIndexTwo.Involutions.FiveFixed

/-!
# Involution fusion in the index-two Ree local kernels

Let H be the core-character or mixed-character kernel, Q = O₂(H), and
E = [Q,Q]. There are involutions in Q − E, and any two are conjugate in H.
For the parity kernel the corresponding orbit is Q − F, with F = C_H(E).
The conjugators are constructed inside H: the coordinate conjugator has zero
binary character, and the marked order-five complement element belongs to
all three kernels. No fusion of arbitrary elements outside Q is asserted.

The actual inclusions identify Q with omega or the full coordinate core and
detect the excluded derived subgroup or its centralizer. The coordinate
involution theorem then supplies a conjugate of root v3. The companion module
computes C_Q(⟨fiveGenerator⟩), including its different centrality behavior in
the parity kernel.

Sources: Aschbacher--Smith, quasithin Lemma 14.2.21, printed p.989 (PDF p.1006);
Aschbacher, *The Tits group as a standard subgroup* (1982), (3.2.7), (3.2.11);
Parrott, *A characterization of the Tits' simple group* (1972), printed p.672.
These are unconditional calculations in the concrete kernels. The parent
assembly retains the ambient model-identification obligations.
-/

@[expose] public section
open Subgroup
namespace ReeTwo.Centralizer.IndexTwo

private theorem root_zero_mem_omega : root 0 ∈ omega := by
  apply Subgroup.mem_map_of_mem
  rw [← Core.binaryCharacter_ker_eq_omega]
  exact Core.binaryCharacter_eq_one_of_square_eq_one _ (by decide +kernel)

private theorem local_isConj_root_zero (L : Subgroup Centralizer) (hω : omega ≤ L)
    (h5 : fiveGenerator ∈ L) (x : L) (u : Core)
    (hu : (SemidirectProduct.inl u : Centralizer) = x)
    (hx : u ^ 2 = 1) (hf : u ∉ centralizer (commutator Core : Set Core)) :
    IsConj (⟨root 0, hω root_zero_mem_omega⟩ : L) x := by
  obtain ⟨h,k,hh,hk⟩ := Core.involution_eq_conjugate_five_root u hx hf
  have hhm : (SemidirectProduct.inl h : Centralizer) ∈ L := by
    apply hω
    apply Subgroup.mem_map_of_mem
    rw [← Core.binaryCharacter_ker_eq_omega]
    change Multiplicative.ofAdd (h.b1 + h.b2 + h.b3) = 1
    rw [hh]
    rfl
  have hc := (SemidirectProduct.inl_aut (φ := Core.complement.subtype)
    ((Core.complementA ^ 2 * Core.complementR) ^ k.val) (Core.root 0)).symm
  have he : fiveGenerator ^ k.val * root 0 * (fiveGenerator ^ k.val)⁻¹ =
      SemidirectProduct.inl ((Core.c ^ k.val) (Core.root 0)) := by
    have hv : Core.complement.subtype ((Core.complementA ^ 2 * Core.complementR) ^ k.val) =
        Core.c ^ k.val := by
      rw [map_pow, map_mul, map_pow]
      rfl
    rw [hv] at hc
    simpa only [fiveGenerator, root, ← map_pow, ← map_inv] using hc
  apply isConj_iff.mpr
  refine ⟨⟨SemidirectProduct.inl h * fiveGenerator ^ k.val, L.mul_mem hhm (L.pow_mem h5 _)⟩, ?_⟩
  apply Subtype.ext
  change (SemidirectProduct.inl h * fiveGenerator ^ k.val) * root 0 *
    (SemidirectProduct.inl h * fiveGenerator ^ k.val)⁻¹ = (x : Centralizer)
  calc
    _ = SemidirectProduct.inl h * (fiveGenerator ^ k.val * root 0 *
          (fiveGenerator ^ k.val)⁻¹) * (SemidirectProduct.inl h)⁻¹ := by group
    _ = SemidirectProduct.inl u := by rw [he, ← map_inv, ← map_mul, ← map_mul, hk]
    _ = x := hu

/-- The actual omega inclusion detects the derived subgroup in either alternative kernel. -/
theorem alternative_mem_derived_iff (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) (u : omega₁ Core (p := 2)) :
    omegaInclusion χ hχ u ∈ ⁅pCore 2 χ.ker, pCore 2 χ.ker⁆ ↔
      (u : Core) ∈ commutator Core := by
  rw [alternative_derived χ hχ]
  exact Subgroup.mem_map_iff_mem SemidirectProduct.inl_injective

/-- Involutions in Q minus its derived subgroup form a single class in either alternative H. -/
theorem alternative_involutions_isConj (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) (x y : χ.ker)
    (hxQ : x ∈ pCore 2 χ.ker) (hyQ : y ∈ pCore 2 χ.ker)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hxE : x ∉ ⁅pCore 2 χ.ker, pCore 2 χ.ker⁆)
    (hyE : y ∉ ⁅pCore 2 χ.ker, pCore 2 χ.ker⁆) : IsConj x y := by
  have horbit (z : χ.ker) (hzQ : z ∈ pCore 2 χ.ker) (hz : z ^ 2 = 1)
      (hzE : z ∉ ⁅pCore 2 χ.ker, pCore 2 χ.ker⁆) :
      IsConj (⟨root 0, omega_le_kernel χ hχ root_zero_mem_omega⟩ : χ.ker) z := by
    obtain ⟨u,rfl⟩ := (omegaInclusion_range χ hχ).symm ▸ hzQ
    have hu : (u : Core) ^ 2 = 1 := by
      have h : u ^ 2 = 1 := (omegaInclusion_injective χ hχ) (by
        simpa only [map_pow, map_one] using hz)
      exact congrArg Subtype.val h
    apply local_isConj_root_zero χ.ker (omega_le_kernel χ hχ) (alternative_five_mem χ hχ)
      (omegaInclusion χ hχ u) u rfl hu
    intro hf
    apply hzE
    apply (alternative_mem_derived_iff χ hχ u).mpr
    rw [← Core.omega_inf_centralizer_derived]
    exact ⟨u.property,hf⟩
  exact (horbit x hxQ hx hxE).symm.trans (horbit y hyQ hy hyE)

/-- There is an involution in Q minus its derived subgroup in both alternative kernels. -/
theorem alternative_exists_involution (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    ∃ x : χ.ker, x ∈ pCore 2 χ.ker ∧ orderOf x = 2 ∧
      x ∉ ⁅pCore 2 χ.ker, pCore 2 χ.ker⁆ := by
  let u : omega₁ Core (p := 2) := ⟨Core.root 0, by
    rw [← Core.binaryCharacter_ker_eq_omega]
    exact Core.binaryCharacter_eq_one_of_square_eq_one _ (by decide +kernel)⟩
  refine ⟨omegaInclusion χ hχ u, ?_, ?_, ?_⟩
  · rw [← omegaInclusion_range χ hχ]
    exact ⟨u,rfl⟩
  · rw [orderOf_injective _ (omegaInclusion_injective χ hχ), ← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  · rw [alternative_mem_derived_iff]
    rw [Core.mem_derived_iff]
    decide +kernel

/-- The parity core inclusion detects the entire derived centralizer of its local group. -/
theorem parity_mem_derived_centralizer_iff (u : Core) :
    parityCoreInclusion u ∈
      centralizer ((⁅pCore 2 parityLocal, pCore 2 parityLocal⁆ : Subgroup parityLocal) : Set parityLocal) ↔
      u ∈ centralizer (commutator Core : Set Core) := by
  rw [parity_centralizer_derived, centralizer_derived_eq_map]
  exact Subgroup.mem_map_iff_mem SemidirectProduct.inl_injective

/-- Involutions in Q minus F form a single class in the parity kernel, with F = C_H([Q,Q]). -/
theorem parity_involutions_isConj (x y : parityLocal)
    (hxQ : x ∈ pCore 2 parityLocal) (hyQ : y ∈ pCore 2 parityLocal)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hxF : x ∉ centralizer ((⁅pCore 2 parityLocal, pCore 2 parityLocal⁆ : Subgroup parityLocal) : Set parityLocal))
    (hyF : y ∉ centralizer ((⁅pCore 2 parityLocal, pCore 2 parityLocal⁆ : Subgroup parityLocal) : Set parityLocal)) :
    IsConj x y := by
  have hω : omega ≤ parityLocal := (Subgroup.map_le_range _ _).trans core_le_parityLocal
  have horbit (z : parityLocal) (hzQ : z ∈ pCore 2 parityLocal) (hz : z ^ 2 = 1)
      (hzF : z ∉ centralizer ((⁅pCore 2 parityLocal, pCore 2 parityLocal⁆ : Subgroup parityLocal) : Set parityLocal)) :
      IsConj (⟨root 0, hω root_zero_mem_omega⟩ : parityLocal) z := by
    obtain ⟨u,rfl⟩ := parityCoreInclusion_range.symm ▸ hzQ
    have hu : u ^ 2 = 1 := by
      apply parityCoreInclusion_injective
      simpa only [map_pow, map_one] using hz
    exact local_isConj_root_zero parityLocal hω character_fiveGenerator
      (parityCoreInclusion u) u rfl hu (fun hf => hzF ((parity_mem_derived_centralizer_iff u).mpr hf))
  exact (horbit x hxQ hx hxF).symm.trans (horbit y hyQ hy hyF)

/-- The parity orbit Q minus F contains an involution. -/
theorem parity_exists_involution :
    ∃ x : parityLocal, x ∈ pCore 2 parityLocal ∧ orderOf x = 2 ∧
      x ∉ centralizer ((⁅pCore 2 parityLocal, pCore 2 parityLocal⁆ : Subgroup parityLocal) : Set parityLocal) := by
  obtain ⟨u,hu,hf⟩ := exists_core_involution_outside_derived_centralizer
  refine ⟨parityCoreInclusion u, ?_, ?_, ?_⟩
  · rw [← parityCoreInclusion_range]
    exact ⟨u,rfl⟩
  · rw [orderOf_injective _ parityCoreInclusion_injective, hu]
  · exact fun h => hf ((parity_mem_derived_centralizer_iff u).mp h)

end ReeTwo.Centralizer.IndexTwo
