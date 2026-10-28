module
public import Theory.PGroupCore

/-!
# Counting a characteristic-two group through its core action

Let K be finite with self-centralizing two-core. Given an equivalence from
that core to a group Q and a homomorphism from Aut(Q) to a finite group A
whose kernel is a two-group, the order of K is at most |A| times its core
order. No chosen action substitutes for intrinsic conjugation on the core.

Transport conjugation by the supplied equivalence. Its kernel centralizes
the core and is therefore a two-group. The composite with the supplied
homomorphism also has two-group kernel. Normality puts this kernel in the
two-core; its image has order at most |A|. The kernel-image order formula
gives the bound.

This general action count is used with the elementary-four quotient of
the middle core in Stellmacher (10.1)(a3), printed p.61, assertion (7),
source `refs/files/stellmacher-n-group.pdf`.
-/

/-- A finite image of the intrinsic core action bounds a characteristic-two
group when the remaining automorphism kernel is a two-group. -/
public theorem card_le_card_mul_core_of_characteristic_two_automorphism_hom
    {K Q A : Type*} [Group K] [Finite K] [Group Q] [Group A] [Finite A]
    (hchar : Subgroup.centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (e : pCore 2 K ≃* Q) (f : MulAut Q →* A) (hf : IsPGroup 2 f.ker) :
    Nat.card K ≤ Nat.card A * Nat.card (pCore 2 K) := by
  let conjugation : K →* MulAut (pCore 2 K) := MulAut.conjNormal
  let action : K →* MulAut Q := (MulAut.congr e).toMonoidHom.comp conjugation
  have hker : action.ker ≤ pCore 2 K := by
    intro g hg
    apply hchar
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have ha : conjugation g = 1 := by
      apply (MulAut.congr e).injective
      exact (MonoidHom.mem_ker.mp hg).trans (map_one (MulAut.congr e)).symm
    have hh := congrArg (fun a : MulAut (pCore 2 K) => (a ⟨q,hq⟩ : K)) ha
    change g*q*g⁻¹=q at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let combined := f.comp action
  have hcombined : IsPGroup 2 combined.ker :=
    hf.comap_of_ker_isPGroup action (pCore_isPGroup.to_le hker)
  have hcombined_le : combined.ker ≤ pCore 2 K := le_sSup ⟨inferInstance,hcombined⟩
  have hkernelcard : Nat.card combined.ker ≤ Nat.card (pCore 2 K) :=
    Subgroup.card_le_of_le hcombined_le
  have himagecard : Nat.card combined.range ≤ Nat.card A :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hcount := combined.ker.card_mul_index
  rw [Subgroup.index_ker] at hcount
  rw [← hcount]
  exact (Nat.mul_le_mul hkernelcard himagecard).trans_eq (Nat.mul_comm _ _)
