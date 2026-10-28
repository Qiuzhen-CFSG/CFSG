module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.CubicParabolics
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.FullAction.SourceFlags

/-!
# The three actual source vertices

The cubic residuals determine their marked maximal subgroups by prime
index. The source flag separates the vertices, and the concrete core
quotients separate the product vertex from the linear ones. Common
maximality then gives all three literal intersections. Residual monotonicity
computes O²(L∩H₃), and cubic nonnormality computes N_H₃(L₂).

The constructor below supplies the exact ambient inputs to the existing
intrinsic G₀ construction. It assumes no maximality, marking, intersection,
normalizer bound or A₃ certificate. The earlier natural flag and the three
actual quotient models remain explicit in this intermediate constructor.
The final constructor takes the two literal full moved-space actions and
only the independently produced S₃ × S₃ middle quotient.

Source: Aschbacher--Smith, 14.4.8 and 14.4.13, printed pp.1009,1012.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
variable {G : Type*} [Group G] [Finite G]

/-- Output geometry on the literal ambient vertices. In particular the
residual is distinguished from the whole point-plane intersection. -/
structure SourceGeometry (L L₁ L₂ X M : Subgroup G) (T : Sylow 2 G) where
  intersection₁₂ : (L ⊔ (T : Subgroup G)) ⊓ (L₁ ⊔ X ⊔ (T : Subgroup G)) =
    L₁ ⊔ (T : Subgroup G)
  intersection₂₃ : (L₁ ⊔ X ⊔ (T : Subgroup G)) ⊓
    (localJoin L₂ X ⊔ (T : Subgroup G)) = X ⊔ (T : Subgroup G)
  intersection₃₁ : (localJoin L₂ X ⊔ (T : Subgroup G)) ⊓
    (L ⊔ (T : Subgroup G)) = L₂ ⊔ (T : Subgroup G)
  parabolics₁ : Quasithin.I5.RankTwoParabolics (L ⊔ (T : Subgroup G) : Subgroup G)
    ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)))
    ((L₁ ⊔ X ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G)))
    ((localJoin L₂ X ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G)))
  parabolics₂ : Quasithin.I5.RankTwoParabolics
    (L₁ ⊔ X ⊔ (T : Subgroup G) : Subgroup G)
    ((T : Subgroup G).subgroupOf (L₁ ⊔ X ⊔ (T : Subgroup G)))
    ((L ⊔ (T : Subgroup G)).subgroupOf (L₁ ⊔ X ⊔ (T : Subgroup G)))
    ((localJoin L₂ X ⊔ (T : Subgroup G)).subgroupOf (L₁ ⊔ X ⊔ (T : Subgroup G)))
  parabolics₃ : Quasithin.I5.RankTwoParabolics
    (localJoin L₂ X ⊔ (T : Subgroup G) : Subgroup G)
    ((T : Subgroup G).subgroupOf (localJoin L₂ X ⊔ (T : Subgroup G)))
    ((L ⊔ (T : Subgroup G)).subgroupOf (localJoin L₂ X ⊔ (T : Subgroup G)))
    ((L₁ ⊔ X ⊔ (T : Subgroup G)).subgroupOf (localJoin L₂ X ⊔ (T : Subgroup G)))
  residual : twoResidual (L ⊓ (localJoin L₂ X ⊔ (T : Subgroup G))) = L₂
  normalizer_eq : (localJoin L₂ X ⊔ (T : Subgroup G)) ⊓ normalizer (L₂ : Set G) =
    L₂ ⊔ (T : Subgroup G)
  parabolic_le_M : L₂ ⊔ (T : Subgroup G) ≤ M
  proper_maximal : IsCoatom ((L₂ ⊔ (T : Subgroup G)).subgroupOf
    (localJoin L₂ X ⊔ (T : Subgroup G)))
  dSystem : Quasithin.I5.DSystem .A3 (IntrinsicSource.actualG0 L T L₁ L₂ X)

/-- Derive the geometry from cubic residuals and actual quotient models.
The six marked maximality hypotheses of the earlier assembly are discharged. -/
noncomputable def source_geometry_of_cubic_quotients
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
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → L ⊔ (T : Subgroup G) ≤ K → K = M)
    (hLM : L ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hMnorm : M ≤ normalizer (L : Set G)) :
    SourceGeometry L L₁ L₂ X M T := by
  let J₁ := L ⊔ (T : Subgroup G)
  let J₂ := L₁ ⊔ X ⊔ (T : Subgroup G)
  let J₃ := localJoin L₂ X ⊔ (T : Subgroup G)
  have hL₁ : L₁ ≤ L := by rw [← hgen]; exact le_sup_left
  have hp₁₁ := linear_marked_coatom T h₁ (hL₁.trans le_sup_left) le_sup_right e₁
  have hp₁₂ := linear_marked_coatom T h₂ (h₂.le_H.trans le_sup_left) le_sup_right e₁
  have hp₂₁ := product_marked_coatom T h₁ (le_sup_left.trans le_sup_left) le_sup_right e₂
  have hp₂₂ := product_marked_coatom T hX (le_sup_right.trans le_sup_left) le_sup_right e₂
  have hp₃₁ := linear_marked_coatom T h₂ (le_sup_left.trans le_sup_left) le_sup_right e₃
  have hp₃₂ := linear_marked_coatom T hX (le_sup_right.trans le_sup_left) le_sup_right e₃
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
  have hpair₁ := linear_cubic_parabolics (J := J₁) T h₁ h₂
    (hL₁.trans le_sup_left) (h₂.le_H.trans le_sup_left) le_sup_right
    (by dsimp [J₁]; rw [sup_sup_sup_comm, sup_idem, hgen]) e₁
  have hpair₂ := product_cubic_parabolics (J := J₂) T h₁ hX
    (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left) le_sup_right
    (by dsimp [J₂]; rw [sup_sup_sup_comm, sup_idem]) e₂
  have hpair₃ := linear_cubic_parabolics (J := J₃) T h₂ hX
    (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left) le_sup_right
    (by dsimp [J₃, localJoin]; rw [sup_sup_sup_comm, sup_idem]) e₃
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
  have hres := source_point_plane_residual L L₂ X T h₂.le_H h₂.residual_eq
    T.isPGroup' h₂.T_normalizes hi₃₁
  have hnorm := source_plane_normalizer L L₂ X T h₂ e₃ hp₃₁
  have hM := sup_le (h₂.le_H.trans hLM) hTM
  exact {
    intersection₁₂ := hi₁₂
    intersection₂₃ := hi₂₃
    intersection₃₁ := hi₃₁
    parabolics₁ := hp₁
    parabolics₂ := hp₂
    parabolics₃ := hp₃
    residual := hres
    normalizer_eq := hnorm
    parabolic_le_M := hM
    proper_maximal := hp₃₁
    dSystem := IntrinsicSource.source_dSystem L L₁ L₂ X M T ⟨e₁⟩ ⟨e₂⟩ ⟨e₃⟩
      hp₁ hp₂ hp₃ hunique hMnorm hres hnorm.le hM hp₃₁ }

/-- All the parabolic clauses of 14.4.8(2), for every actual Y-member.
I₂ itself is not identified with the whole parabolic; its join with T is. -/
theorem FullMovedSpaceAction.parabolics
    {H K I₂ U L₂ V₂ E X : Subgroup G} {T : Sylow 2 G}
    (d : FullMovedSpaceAction T I₂ L₂ V₂ X)
    (hX : X ∈ YFamily H T V₂ E) (h₂ : ThreeExtension K T L₂)
    (hI : I₂ = L₂ ⊔ U) (hUT : U ≤ T) :
    Quasithin.I5.RankTwoParabolics (localJoin L₂ X ⊔ (T : Subgroup G) : Subgroup G)
      ((T : Subgroup G).subgroupOf (localJoin L₂ X ⊔ (T : Subgroup G)))
      ((I₂ ⊔ (T : Subgroup G)).subgroupOf (localJoin L₂ X ⊔ (T : Subgroup G)))
      ((X ⊔ (T : Subgroup G)).subgroupOf (localJoin L₂ X ⊔ (T : Subgroup G))) := by
  rw [source_I₂_join_T I₂ L₂ U T hI hUT]
  exact linear_cubic_parabolics T h₂ hX.1 (le_sup_left.trans le_sup_left)
    (le_sup_right.trans le_sup_left) le_sup_right
    (by dsimp [localJoin]; rw [sup_sup_sup_comm, sup_idem]) d.quotient

/-- Apply the constructed full actions to the actual source geometry.
No action or quotient marking is changed, and no geometric conclusion is an input. -/
noncomputable def source_geometry_of_full_actions
    (H M L L₁ L₂ V₁ V₂ V E X I₂ : Subgroup G) (T : Sylow 2 G)
    (hN : NaturalFlagData H T V₁ V₂ V E L L₁ L₂)
    (hX : X ∈ YFamily H T V₂ E) (hne : X ≠ L₁)
    (a₁ : FullMovedSpaceAction T I₂ L₂ V₂ L₁)
    (aX : FullMovedSpaceAction T I₂ L₂ V₂ X)
    (e₂ : coreQuotient (L₁ ⊔ X ⊔ (T : Subgroup G)) ≃* SymmetricThreeProduct.G)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → L ⊔ (T : Subgroup G) ≤ K → K = M)
    (hLM : L ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hMnorm : M ≤ normalizer (L : Set G)) : SourceGeometry L L₁ L₂ X M T := by
  have hjoin : localJoin L₂ L₁ = L := by
    dsimp [localJoin]
    rw [sup_comm, hN.generated]
  have e₁ : coreQuotient (L ⊔ (T : Subgroup G)) ≃* Matrix.PSL3Two.PSL :=
    hjoin ▸ a₁.quotient
  exact source_geometry_of_cubic_quotients L L₁ L₂ X H M T hN.L₁_three hN.L₂_three hX.1
    hne hN.generated hN.flag_intersection (source_index_three T L₁ hN.L₁_three)
    e₁ e₂ aX.quotient hunique hLM hTM hMnorm

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
