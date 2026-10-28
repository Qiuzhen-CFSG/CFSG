module
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.NormalClosureCentralizerCore

/-!
# A simple factor with a two-group supplement

If K is a nonabelian simple normal subgroup and R is a two-subgroup,
then the centralizer of K in KR is trivial when O₂(KR) is trivial.
The centralizer embeds in the two-group quotient, so it lies in O₂(KR).
All normality and core calculations are relative to the literal join.

Source application: Aschbacher--Smith 13.1.9, printed p.871, lifting
the actor containment from the common chief section to the action on D.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {Q : Type*} [Group Q]

theorem centralizer_inf_sup_eq_bot_of_simple_two_supplement (K R : Subgroup Q)
    [K.Normal] [IsSimpleGroup K] (hn : ¬ IsMulCommutative K)
    (hR : IsPGroup 2 R) (hc : pCore 2 (K ⊔ R : Subgroup Q) = ⊥) :
    (K ⊔ R) ⊓ centralizer (K : Set Q) = ⊥ := by
  let E := K ⊔ R
  let K₀ := K.subgroupOf E
  have hKE : K ≤ E := le_sup_left
  let : IsSimpleGroup K₀ := (subgroupOfEquivOfLe hKE).isSimpleGroup
  have hn₀ : ¬ IsMulCommutative K₀ := by
    intro hn₀
    let := hn₀
    apply hn
    apply isMulCommutative_iff.mpr
    intro x y
    obtain ⟨a,rfl⟩ := (subgroupOfEquivOfLe hKE).surjective x
    obtain ⟨b,rfl⟩ := (subgroupOfEquivOfLe hKE).surjective y
    rw [← map_mul, ← map_mul, (isMulCommutative_iff.mp hn₀) a b]
  have hq : IsPGroup 2 (E ⧸ K₀) :=
    isPGroup_quotient_of_sup_eq_top K₀ (R.subgroupOf E) hR.comap_subtype
      (by rw [← subgroupOf_sup le_sup_left le_sup_right]; exact subgroupOf_self E)
  have hh := centralizer_eq_bot_of_simple_two_quotient K₀ hn₀ hq hc
  have hm := congrArg (Subgroup.map E.subtype) hh
  change (centralizer (K.subgroupOf E : Set E)).map E.subtype = (⊥ : Subgroup E).map E.subtype at hm
  rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hKE,Subgroup.map_bot] at hm
  exact hm
end Theory.GroupTheory

