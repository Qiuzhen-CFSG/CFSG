module
public import Theory.GroupTheory.CComponent.QuasisimpleImageRigidity
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel

/-!
# Small images of strict local component extensions

Suppose a C-component D with quasisimple two-core quotient properly
contains a perfect subgroup A with simple two-core quotient. If O₂(D)
normalizes A, every homomorphism from D to a group no larger than
A/O₂(A) is trivial. Otherwise its kernel is solvable; the image of A
has at least the quotient order and hence fills the target. Thus A
supplements the radical of D, and quasisimple supplement rigidity gives
A = D, a contradiction.

Source application: the small elementary normal subgroup branch of
Aschbacher--Smith 12.9.3, printed pp.858--859, using A.3.3 and A.3.11.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- A strict simple-core section prevents a containing component from acting
nontrivially on a group no larger than that section. -/
theorem IsCComponent.hom_eq_one_of_strict_simple_section
    {A D : Subgroup G} (hD : D.IsCComponent) (hAD : A < D)
    [Group.IsPerfect A] [IsSimpleGroup (A ⧸ pCore 2 A)]
    [IsQuasisimple (D ⧸ pCore 2 D)]
    (hn : pCore 2 D ≤ normalizer (A.subgroupOf D : Set D))
    (f : D →* H) (hcard : Nat.card H ≤ Nat.card (A ⧸ pCore 2 A)) : f = 1 := by
  by_contra hf
  have hk : f.ker ≠ ⊤ := by
    intro ht
    apply hf
    ext x
    exact (show x ∈ f.ker from ht ▸ mem_top x)
  let : Group.IsSolvable f.ker :=
    hD.isSolvable_of_subnormal_lt_top (inferInstance : f.ker.Normal).isSubnormal hk
  let i := inclusion hAD.le
  let g := f.comp i
  let : Group.IsSolvable g.ker := Group.isSolvable_of_isSolvable_injective
    (f := i.subgroupComap f.ker) (fun x y hh => Subtype.ext ((inclusion_injective hAD.le) (congrArg Subtype.val hh)))
  let : Group.IsSolvable g.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  let e := PerfectCoreTwoExtension.solvableKernelQuotientEquiv g.rangeRestrict
    g.rangeRestrict_surjective
  have hle : Nat.card H ≤ Nat.card g.range := hcard.trans
    ((Nat.card_congr e.toEquiv).trans_le
      (Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card _)))
  have hg : Function.Surjective g := MonoidHom.range_eq_top.mp
    (g.range.eq_top_of_card_eq (le_antisymm (card_le_card_group _) hle))
  have hcover : A.subgroupOf D ⊔ f.ker = ⊤ := by
    apply top_unique
    intro d _
    obtain ⟨a,ha⟩ := hg (f d)
    apply mem_sup_of_normal_right.mpr
    refine ⟨i a,a.property,(i a)⁻¹*d,?_,by simp⟩
    change f ((i a)⁻¹*d) = 1
    rw [map_mul,map_inv]
    change (g a)⁻¹ * f d = 1
    rw [ha,inv_mul_cancel]
  let := hD.perfect
  have hrad : solvableRadical D ⊔ A.subgroupOf D = ⊤ := by
    apply top_unique
    rw [←hcover]
    exact sup_le le_sup_right
      ((le_solvableRadical f.ker inferInstance inferInstance).trans le_sup_left)
  have he := eq_top_of_radical_supplement_of_quasisimple_quotient
    (pCore 2 D) (A.subgroupOf D) hn hrad
  exact hAD.not_ge (subgroupOf_eq_top.mp he)
end Theory.GroupTheory
