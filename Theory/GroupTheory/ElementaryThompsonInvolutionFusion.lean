module

public import Stellmacher.ElementaryAbelianMaxFusion
public import Theory.GroupTheory.Involution.Basic

/-!
# Involution fusion through an abelian elementary Thompson subgroup

If every involution of E is E-conjugate into the abelian J(T), and
N_G(J(T)) lies in E, Burnside fusion controls all involutions of E.
Weak closure of J(T) is proved by the maximum elementary subgroup API;
it is not an additional fusion assumption.

Source application: Aschbacher–Smith 13.4.9, printed p.906, with
J(T)=O₂(H₀). The four concrete symplectic classes supply the representatives.
-/

public section
open Subgroup BenderSuzuki.PFAppendixIII
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- Burnside fusion in the actual abelian elementary Thompson subgroup. -/
theorem abelian_maxJ_controls_element_fusion (T : Sylow 2 G)
    [IsMulCommutative (elementaryAbelianMaxJ (T : Subgroup G))]
    {x y : G} (hx : x ∈ elementaryAbelianMaxJ (T : Subgroup G))
    (hy : y ∈ elementaryAbelianMaxJ (T : Subgroup G)) (hxy : IsConj x y) :
    ∃ n ∈ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G),
      MulAut.conj n x = y := by
  exact T.weakly_closed_normalizer_controls_centralizer_fusion _
    (sSup_le fun _ hA => hA.1) (maxJ_weakly_closed_normalizer T)
    ((elementaryAbelianMaxJ (T : Subgroup G)).le_centralizer hx)
    ((elementaryAbelianMaxJ (T : Subgroup G)).le_centralizer hy) hxy

/-- Representatives in J(T) extend Burnside fusion to every involution of E. -/
theorem involution_fusion_of_abelian_maxJ (T : Sylow 2 G) (E : Subgroup G)
    [IsMulCommutative (elementaryAbelianMaxJ (T : Subgroup G))]
    (hn : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ E)
    (hr : ∀ a ∈ E, BenderSuzuki.PFAppendixIII.IsInvolution a →
      ∃ c ∈ E, MulAut.conj c a ∈ elementaryAbelianMaxJ (T : Subgroup G)) :
    ∀ a ∈ E, ∀ b ∈ E, BenderSuzuki.PFAppendixIII.IsInvolution a → IsConj a b →
      ∃ c ∈ E, MulAut.conj c a = b := by
  intro a ha b hb hai hab
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  have hbi : BenderSuzuki.PFAppendixIII.IsInvolution b := by
    rw [← hg]
    refine ⟨fun he => hai.1 ((MulAut.conj g).injective
      (he.trans (map_one _).symm)), ?_⟩
    change (MulAut.conj g a) ^ 2 = 1
    rw [← map_pow, hai.2, map_one]
  obtain ⟨x, hx, hxa⟩ := hr a ha hai
  obtain ⟨y, hy, hyb⟩ := hr b hb hbi
  have hconj : IsConj (MulAut.conj x a) (MulAut.conj y b) :=
    (isConj_iff.mpr ⟨x, rfl⟩).symm.trans
      (hab.trans (isConj_iff.mpr ⟨y, rfl⟩))
  obtain ⟨n, hnW, he⟩ := abelian_maxJ_controls_element_fusion T hxa hyb hconj
  refine ⟨y⁻¹ * n * x, E.mul_mem (E.mul_mem (E.inv_mem hy) (hn hnW)) hx, ?_⟩
  have hh := congrArg (MulAut.conj y⁻¹) he
  simpa only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc,
    inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using hh

end Stellmacher
