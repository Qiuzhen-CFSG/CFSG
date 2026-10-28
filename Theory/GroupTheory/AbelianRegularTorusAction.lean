module
public import Theory.GroupTheory.MarkedInternalProduct
/-!
# Abelian overgroups of a regular torus

An abelian group has the same automorphism image as any subgroup acting
regularly on the nonidentity elements. A second faithful torus is disjoint
from a factor centralizing its action domain, so the two form an internal
direct product. These elementary action arguments preserve the actual factors.

Source: Aschbacher–Smith, Lemma 2.4.8(6), printed p.529.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

theorem torus_directProduct_of_free_centralized_subgroup
    (B D E Z : Subgroup G) [IsMulCommutative B]
    (hgen : D ⊔ E = B) (hDZ : D ≤ centralizer (Z : Set G)) (hZ : Z ≠ ⊥)
    (hfree : ∀ e ∈ E, ∀ z ∈ Z, z ≠ 1 → e*z*e⁻¹=z → e=1) :
    Disjoint D E ∧ Nonempty (B ≃* D × E) := by
  obtain ⟨z,hz,hz1⟩ := Z.bot_or_exists_ne_one.resolve_left hZ
  have hd : Disjoint D E := disjoint_def.mpr (by
    intro e heD heE
    apply hfree e heE z hz hz1
    rw [←(mem_centralizer_iff.mp (hDZ heD)) z hz,mul_inv_cancel_right])
  have hc : D ≤ centralizer (E : Set G) := by
    intro d hd e he
    exact congrArg Subtype.val (mul_comm' (⟨e,le_sup_right.trans_eq hgen he⟩ : B)
      ⟨d,le_sup_left.trans_eq hgen hd⟩)
  obtain ⟨f,_,_⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv B D E hgen hd hc
  exact ⟨hd,⟨f⟩⟩

theorem abelian_action_range_eq_of_regular_subgroup
    {V : Type*} [Group V] (B D : Subgroup G) [IsMulCommutative B]
    (hDB : D ≤ B) (ρ : B →* MulAut V) (v : V) (hv : v ≠ 1)
    (htrans : ∀ w : V, w ≠ 1 → ∃ d : D, ρ (inclusion hDB d) v = w) :
    ρ.range = (ρ.comp (inclusion hDB)).range := by
  apply le_antisymm _ (by rintro _ ⟨d,rfl⟩;exact ⟨inclusion hDB d,rfl⟩)
  rintro _ ⟨b,rfl⟩
  have hbv : ρ b v ≠ 1 := fun he => hv ((ρ b).map_eq_one_iff.mp he)
  obtain ⟨d,hd⟩ := htrans (ρ b v) hbv
  refine ⟨d,?_⟩
  apply MulEquiv.ext
  intro w
  by_cases hw : w = 1
  · rw [hw]
    simp
  obtain ⟨c,rfl⟩ := htrans w hw
  have hcomm (a b : B) : Commute (ρ a) (ρ b) :=
    ((show Commute a b from mul_comm' a b).map ρ)
  change (ρ (inclusion hDB d)) ((ρ (inclusion hDB c)) v) = ρ b ((ρ (inclusion hDB c)) v)
  have he (a b : B) : ρ a (ρ b v) = ρ b (ρ a v) :=
    DFunLike.congr_fun (hcomm a b).eq v
  rw [he (inclusion hDB d) (inclusion hDB c),he b (inclusion hDB c),hd]

end Subgroup
