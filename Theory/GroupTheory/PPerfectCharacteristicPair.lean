module
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Perfect actors fixing a characteristic subgroup and quotient

A p-perfect group acting trivially on a characteristic p-subgroup and its
quotient acts trivially on the whole finite group: the paired-action kernel
is a p-group. The subgroup application uses literal conjugation and an
embedded p-core commutator bound.

This is the automorphism-kernel step used after the A4 recognition in
Aschbacher--Smith, proof of 15.4.18, p.1163.
-/

public section
open Subgroup
namespace IsPPerfect
variable {A B : Type*} [Group A] [Finite A] [Group B]

/-- Triviality on both characteristic layers forces the whole action to be trivial. -/
theorem hom_eq_one_of_characteristic_pair {p : ℕ} [Fact (Nat.Prime p)] (hB : IsPPerfect p B)
    (C : Subgroup A) [C.Characteristic] (hC : IsPGroup p C) (f : B →* MulAut A)
    (hfix : ∀ b (c : C), f b c = c)
    (hquot : ∀ b a, QuotientGroup.mk' C (f b a) = QuotientGroup.mk' C a) : f = 1 := by
  have hr : f.range ≤ (automorphismPair C).ker := by
    rintro _ ⟨b,rfl⟩
    change automorphismPair C (f b) = 1
    rw [automorphismPair_apply]
    apply Prod.ext
    · apply MulEquiv.ext
      intro c
      exact Subtype.ext (hfix b c)
    · apply MulEquiv.ext
      intro a
      induction a using QuotientGroup.induction_on with
      | H a =>
        change quotientAut C (f b) (QuotientGroup.mk' C a) = QuotientGroup.mk' C a
        rw [quotientAut_apply_mk]
        exact hquot b a
  have hp : IsPGroup p f.range := (isPGroup_automorphism_pair_kernel C hC).to_le hr
  have he := hB.hom_eq_one_of_isPGroup hp f.rangeRestrict
  apply MonoidHom.ext
  intro b
  exact congrArg Subtype.val (DFunLike.congr_fun he b)

end IsPPerfect

open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A p-perfect actor fixing the core and its quotient centralizes the group. -/
theorem le_centralizer_of_pPerfect_of_core {p : ℕ} [Fact (Nat.Prime p)]
    (A B : Subgroup G) (hB : IsPPerfect p B)
    (hn : B ≤ normalizer (A : Set G))
    (hc : B ≤ centralizer (A.pCoreIn p : Set G))
    (hcomm : ⁅B,A⁆ ≤ A.pCoreIn p) : B ≤ centralizer (A : Set G) := by
  let f : B →* MulAut A := A.normalizerMonoidHom.comp (inclusion hn)
  have hf : f = 1 := hB.hom_eq_one_of_characteristic_pair (pCore p A) pCore_isPGroup f
    (fun b c => by
      apply Subtype.ext
      change (b : G) * (c : G) * (b : G)⁻¹ = (c : G)
      rw [← hc b.property c (mem_map_of_mem A.subtype c.property)]
      simp only [mul_assoc, mul_inv_cancel, mul_one])
    (fun b a => by
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hmem : (((f b a / a : A) : G)) ∈ A.pCoreIn p := by
        change ((b : G) * (a : G) * (b : G)⁻¹) / (a : G) ∈ A.pCoreIn p
        rw [div_eq_mul_inv, ← commutatorElement_def]
        exact hcomm (commutator_mem_commutator b.property a.property)
      obtain ⟨v,hv,he⟩ := hmem
      exact (Subtype.ext he : v = f b a / a) ▸ hv)
  intro b hb a ha
  have he := congrArg (fun t : B →* MulAut A =>
    ((t ⟨b,hb⟩ ⟨a,ha⟩ : A) : G)) hf
  change b * a * b⁻¹ = a at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end Subgroup
