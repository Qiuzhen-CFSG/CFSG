module

public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupAction.NormalComplement

/-!
# A central Sylow center and an abelian image

Suppose the center of a Sylow p-subgroup S is central in the finite
ambient group A. For any homomorphism from A into an abelian group,
either its kernel contains a nontrivial central normal subgroup, or A
has a normal p-complement. The central subgroup is exactly Z(S) ∩ ker(q),
with Z(S) mapped into A.

If that intersection is trivial, the kernel restricted to S is trivial:
a nontrivial normal subgroup of S must meet Z(S). The abelian image then
makes S abelian, so S = Z(S) is central in A. Burnside transfer applies.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Sylow
variable {A D : Type*} [Group A] [Finite A] [Group D] [IsMulCommutative D]
  {p : ℕ} [Fact p.Prime]

/-- A central Sylow center either supplies a nontrivial central subgroup
of an abelian-image kernel or forces a normal p-complement. -/
theorem hasNormalPComplement_or_central_kernel
    (S : Sylow p A) (q : A →* D)
    (hZ : (center S).map (S : Subgroup A).subtype ≤ center A) :
    HasNormalPComplement p A ∨
      ∃ N : Subgroup A, N.Normal ∧ N ≠ ⊥ ∧ N ≤ center A ∧ N ≤ q.ker := by
  let Z := (center S).map (S : Subgroup A).subtype
  let N := Z ⊓ q.ker
  by_cases hN : N = ⊥
  · apply Or.inl
    let f := q.comp (S : Subgroup A).subtype
    have hk : f.ker = ⊥ := by
      by_contra hn
      have hmeet := center_inf_ne_bot_of_normal S.isPGroup' f.ker hn
      apply hmeet
      apply bot_unique
      intro x hx
      apply Subtype.ext
      have hm : (x : A) ∈ N := ⟨mem_map_of_mem (S : Subgroup A).subtype hx.1,hx.2⟩
      rw [hN,mem_bot] at hm
      exact hm
    have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hk
    let : IsMulCommutative S := ⟨⟨fun x y => hf (by simp only [map_mul,mul_comm])⟩⟩
    have hS : (S : Subgroup A) ≤ center A := by
      intro x hx
      apply hZ
      exact mem_map_of_mem (S : Subgroup A).subtype
        ((center_eq_top (G := S)).symm ▸ (mem_top (⟨x,hx⟩ : S)))
    exact exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer p S
      (le_inf S.le_normalizer (hS.trans (center_le_centralizer _)))
  · apply Or.inr
    have hNZ : N ≤ center A := inf_le_left.trans hZ
    have hnormal : N.Normal := ⟨fun x hx a => by
      rw [mem_center_iff.mp (hNZ hx) a,mul_assoc,mul_inv_cancel,mul_one]
      exact hx⟩
    exact ⟨N,hnormal,hN,hNZ,inf_le_right⟩

end Sylow
