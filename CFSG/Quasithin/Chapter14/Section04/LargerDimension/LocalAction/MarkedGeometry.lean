module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Geometry
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.IntrinsicSystem

/-!
# Local-action geometry for the large-dimensional branch

The conditional assembly below proves the ambient deductions required by
14.4.13 from the three genuine core quotients and the marked maximality
calculations. It derives vertex distinctness, all three literal intersections,
every clause of the three RankTwoParabolics records, the residual identity
O²(L ∩ H₃) = L₂, and the relative normalizer bound. The existing intrinsic
assembly then supplies D4 and the D-system on the actual generated group G₀.

The input flag identity and index-three fact concern the earlier natural
module from 12.8 and 14.3. Normality and uniqueness of M are 14.3.3(1--2).
The middle quotient is supplied by the surviving 14.4.10--12 model branches.
The two linear quotients and marked maximality still require the full action
and component argument of 14.4.8. This file does not claim that argument, the
membership L₁ ∈ Y, or the source classification is complete.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.4.8 and 14.4.13, printed pp.1009 and 1012. In particular, the source I₂
is kept distinct from I₂T = L₂T, and L ∩ H₃ from its two-residual.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
variable {G : Type*} [Group G] [Finite G]

/-- Construct the actual intrinsic A₃ system once the source action and
marked maximality calculations have been supplied. No ambient intersections,
residual-normalizer conclusions, chamber equality, or A₃ assembly record
are assumptions. -/
noncomputable def source_dSystem_of_marked_maximality
    (L L₁ L₂ X H M : Subgroup G) (T : Sylow 2 G)
    (h₁ : ThreeExtension H T L₁) (h₂ : ThreeExtension L T L₂)
    (hX : ThreeExtension H T X) (hne : X ≠ L₁)
    (hgen : L₁ ⊔ L₂ = L)
    (hflag : (L ⊔ (T : Subgroup G)) ⊓ H = L₁ ⊔ (T : Subgroup G))
    (hindex : ((T : Subgroup G).subgroupOf (L₁ ⊔ (T : Subgroup G))).index = 3)
    (e₁ : coreQuotient (L ⊔ (T : Subgroup G)) ≃* Matrix.PSL3Two.PSL)
    (e₂ : coreQuotient (L₁ ⊔ X ⊔ (T : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (e₃ : coreQuotient (localJoin L₂ X ⊔ (T : Subgroup G)) ≃* Matrix.PSL3Two.PSL)
    (hp₁₁ : IsCoatom ((L₁ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))))
    (hp₁₂ : IsCoatom ((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))))
    (hp₂₁ : IsCoatom ((L₁ ⊔ (T : Subgroup G)).subgroupOf
      (L₁ ⊔ X ⊔ (T : Subgroup G))))
    (hp₂₂ : IsCoatom ((X ⊔ (T : Subgroup G)).subgroupOf
      (L₁ ⊔ X ⊔ (T : Subgroup G))))
    (hp₃₁ : IsCoatom ((L₂ ⊔ (T : Subgroup G)).subgroupOf
      (localJoin L₂ X ⊔ (T : Subgroup G))))
    (hp₃₂ : IsCoatom ((X ⊔ (T : Subgroup G)).subgroupOf
      (localJoin L₂ X ⊔ (T : Subgroup G))))
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → L ⊔ (T : Subgroup G) ≤ K → K = M)
    (hLM : L ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hMnorm : M ≤ normalizer (L : Set G)) :
    Quasithin.I5.DSystem .A3 (IntrinsicSource.actualG0 L T L₁ L₂ X) := by
  let J₁ := L ⊔ (T : Subgroup G)
  let J₂ := L₁ ⊔ X ⊔ (T : Subgroup G)
  let J₃ := localJoin L₂ X ⊔ (T : Subgroup G)
  have hL₁ : L₁ ≤ L := by rw [← hgen]; exact le_sup_left
  have hsep : ¬ X ≤ J₁ := source_actor_separation L L₁ X H T h₁ hX hne hflag hindex
  have h₁₂ : J₁ ≠ J₂ := by
    intro he
    apply hsep
    rw [he]
    exact le_sup_right.trans le_sup_left
  have h₃₁ : J₃ ≠ J₁ := by
    intro he
    apply hsep
    rw [← he]
    exact le_sup_right.trans le_sup_left
  have h₂₃ : J₂ ≠ J₃ := by
    have hc₂ : Nat.card (coreQuotient J₂) = 36 := by
      rw [Nat.card_congr e₂.toEquiv]
      norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm]
    have hc₃ : Nat.card (coreQuotient J₃) = 168 :=
      (Nat.card_congr e₃.toEquiv).trans Matrix.PSL3Two.card_PSL
    intro he
    rw [he] at hc₂
    omega
  obtain ⟨hi₁₂, hi₂₃, hi₃₁⟩ := source_intersections L L₁ L₂ X T hL₁ h₂.le_H
    h₁₂ h₂₃ h₃₁ hp₁₁ hp₁₂ hp₂₁ hp₂₂ hp₃₁ hp₃₂
  have hpair₁ := linear_vertex_parabolics T J₁ (L₁ ⊔ (T : Subgroup G))
    (L₂ ⊔ (T : Subgroup G)) (sup_le_sup_right hL₁ _)
    (sup_le_sup_right h₂.le_H _) le_sup_right le_sup_right
    (by dsimp [J₁]; rw [sup_sup_sup_comm, sup_idem, hgen]) e₁ hp₁₁ hp₁₂
  have hpair₂ := product_vertex_parabolics T J₂ (L₁ ⊔ (T : Subgroup G))
    (X ⊔ (T : Subgroup G)) (sup_le_sup_right le_sup_left _)
    (sup_le_sup_right le_sup_right _) le_sup_right le_sup_right
    (by dsimp [J₂]; rw [sup_sup_sup_comm, sup_idem]) e₂ hp₂₁ hp₂₂
  have hpair₃ := linear_vertex_parabolics T J₃ (L₂ ⊔ (T : Subgroup G))
    (X ⊔ (T : Subgroup G)) (sup_le_sup_right le_sup_left _)
    (sup_le_sup_right le_sup_right _) le_sup_right le_sup_right
    (by dsimp [J₃, localJoin]; rw [sup_sup_sup_comm, sup_idem]) e₃ hp₃₁ hp₃₂
  have hp₁ : Quasithin.I5.RankTwoParabolics J₁ ((T : Subgroup G).subgroupOf J₁)
      (J₂.subgroupOf J₁) (J₃.subgroupOf J₁) := by
    rw [← inf_subgroupOf_left J₂ J₁, ← inf_subgroupOf_right J₃ J₁,
      hi₁₂, hi₃₁]
    exact hpair₁
  have hp₂ : Quasithin.I5.RankTwoParabolics J₂ ((T : Subgroup G).subgroupOf J₂)
      (J₁.subgroupOf J₂) (J₃.subgroupOf J₂) := by
    rw [← inf_subgroupOf_right J₁ J₂, ← inf_subgroupOf_left J₃ J₂,
      hi₁₂, hi₂₃]
    exact hpair₂
  have hp₃ : Quasithin.I5.RankTwoParabolics J₃ ((T : Subgroup G).subgroupOf J₃)
      (J₁.subgroupOf J₃) (J₂.subgroupOf J₃) := by
    rw [← inf_subgroupOf_left J₁ J₃, ← inf_subgroupOf_right J₂ J₃,
      hi₃₁, hi₂₃]
    exact hpair₃
  exact IntrinsicSource.source_dSystem L L₁ L₂ X M T ⟨e₁⟩ ⟨e₂⟩ ⟨e₃⟩
    hp₁ hp₂ hp₃ hunique hMnorm
    (source_point_plane_residual L L₂ X T h₂.le_H h₂.residual_eq T.isPGroup'
      h₂.T_normalizes hi₃₁)
    (source_plane_normalizer L L₂ X T h₂ e₃ hp₃₁).le
    (sup_le (h₂.le_H.trans hLM) hTM) hp₃₁

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
