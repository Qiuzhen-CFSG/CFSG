module

public import Theory.GroupAction.PResidualCentralProduct
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# A residual escaping a centralizer-generated subgroup

Let a Sylow two-subgroup T of C normalize W. If the two-residual of M ∩ C
centralizes W, then a noncentral two-residual of C cannot be covered by
M ∩ C together with its centralizer of W. Indeed, the Sylow supplements
would express C as AT with A centralizing W, forcing its action on W to
have two-group image.

This is the escape inequality in Aschbacher--Smith15.1.14(1), printed p.1091.
It does not assert that minimal descent preserves a noncentral residual.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem residual_sup_sylow (T : Sylow 2 G) (C : Subgroup G)
    (hTC : (T : Subgroup G) ≤ C) :
    (pResidual 2 C).map C.subtype ⊔ (T : Subgroup G) = C := by
  have he := congrArg (map C.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTC))
  rwa [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTC] at he

theorem residual_escape_of_not_centralizes
    (T : Sylow 2 G) (C M W : Subgroup G)
    (hTC : (T : Subgroup G) ≤ C) (hTM : (T : Subgroup G) ≤ M)
    (hTN : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hres : (pResidual 2 (M ⊓ C : Subgroup G)).map (M ⊓ C).subtype ≤ centralizer (W : Set G))
    (hnot : ¬ (pResidual 2 C).map C.subtype ≤ centralizer (W : Set G)) :
    ¬ (pResidual 2 C).map C.subtype ≤
      (M ⊓ C) ⊔ ((pResidual 2 C).map C.subtype ⊓ centralizer (W : Set G)) := by
  let R := (pResidual 2 C).map C.subtype
  let B := R ⊓ centralizer (W : Set G)
  let A := (pResidual 2 (M ⊓ C : Subgroup G)).map (M ⊓ C).subtype ⊔ B
  intro hle
  have hCT : C ≤ A ⊔ (T : Subgroup G) := by
    rw [← residual_sup_sylow T C hTC]
    apply sup_le ?_ le_sup_right
    apply hle.trans
    apply sup_le
    · rw [← residual_sup_sylow T (M ⊓ C) (le_inf hTM hTC)]
      exact sup_le_sup le_sup_left le_rfl
    · exact (show B ≤ A from le_sup_right).trans le_sup_left
  have hAC : A ≤ centralizer (W : Set G) := sup_le hres inf_le_right
  exact hnot ((embedded_pResidual_mono 2 hCT).trans
    (pResidual_join_le_centralizer 2 A T W hAC hTN T.isPGroup'))


end Subgroup
