module
public import Theory.GroupAction.ModelConjugation
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Two-residuals and a centralized factor

If A centralizes Z and a p-group B normalizes Z, the action of A joined with B
on Z has p-group image. Consequently its p-residual centralizes Z.

Source application: Aschbacher--Smith, 2.4.29, printed p.545.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
theorem pResidual_join_le_centralizer (p : ℕ) (A B Z : Subgroup G)
    (hAZ : A ≤ centralizer (Z : Set G)) (hBn : B ≤ normalizer (Z : Set G))
    (hB : IsPGroup p B) :
    (pResidual p (A ⊔ B : Subgroup G)).map (A ⊔ B).subtype ≤ centralizer (Z : Set G) := by
  let F := A ⊔ B
  have hFn : F ≤ normalizer (Z : Set G) :=
    sup_le (hAZ.trans (Subgroup.centralizer_le_normalizer _)) hBn
  let f := Theory.GroupAction.ModelConjugation.action F Z hFn (MulEquiv.refl Z)
  have hfker : f.ker = (centralizer (Z : Set G)).subgroupOf F :=
    Theory.GroupAction.ModelConjugation.action_ker F Z hFn (MulEquiv.refl Z)
  have hAf : (A.subgroupOf F).map f = ⊥ := by
    apply (map_eq_bot_iff _).mpr
    rw [hfker]
    exact fun _ h => hAZ h
  have hr : f.range = (B.subgroupOf F).map f := by
    have hs : A.subgroupOf F ⊔ B.subgroupOf F = ⊤ := by
      rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
    rw [MonoidHom.range_eq_map,←hs,Subgroup.map_sup,hAf,bot_sup_eq]
  have hp : IsPGroup p f.range := by
    rw [hr]
    exact (hB.of_equiv (subgroupOfEquivOfLe (show B ≤ F from le_sup_right)).symm).map f
  have hk := pResidual_le_ker_of_isPGroup p f.rangeRestrict hp
  rintro z ⟨a,ha,rfl⟩
  have ha' : a ∈ f.ker := by
    have hh := hk ha
    change f.rangeRestrict a = 1 at hh
    exact congrArg Subtype.val hh
  rw [hfker] at ha'
  exact ha'
end Subgroup
