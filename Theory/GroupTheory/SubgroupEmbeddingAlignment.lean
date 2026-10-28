module
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Tactic.Group

/-!
# Aligning a subgroup embedding by inner conjugation

An ambient isomorphism carrying an embedded subgroup onto a subgroup with
only inner automorphisms can be adjusted to agree pointwise with the original
embedding. Restrict the comparison, realize that restriction by conjugation,
and undo the same conjugation in the ambient group.
-/

public noncomputable section
namespace Subgroup

theorem exists_aligned_equiv_of_inner_automorphisms {G K : Type*} [Group G] [Group K]
    (P : Subgroup K) (j : P →* G) (hj : Function.Injective j)
    (e : G ≃* K) (he : j.range.map e.toMonoidHom = P)
    (hinner : ∀ a : MulAut P, ∃ p : P, a = MulAut.conj p) :
    ∃ f : G ≃* K, ∀ x : P, f (j x) = x := by
  let k : P →* P := (e.toMonoidHom.comp j).codRestrict P (fun x =>
    by
      have hx : e (j x) ∈ j.range.map e.toMonoidHom :=
        mem_map_of_mem e.toMonoidHom (show j x ∈ j.range from ⟨x,rfl⟩)
      change e (j x) ∈ P
      exact he.le hx)
  have hki : Function.Injective k := by
    intro a b hab
    exact hj (e.injective (congrArg Subtype.val hab))
  have hks : Function.Surjective k := by
    intro x
    have hx : x.val ∈ j.range.map e.toMonoidHom := he.ge x.property
    obtain ⟨y,⟨a,rfl⟩,ha⟩ := hx
    exact ⟨a,Subtype.ext ha⟩
  let a : MulAut P := MulEquiv.ofBijective k ⟨hki,hks⟩
  obtain ⟨p,hp⟩ := hinner a
  refine ⟨e.trans (MulAut.conj (p.val⁻¹)),fun x => ?_⟩
  have hx : e (j x) = p.val * x.val * p.val⁻¹ :=
    congrArg Subtype.val (DFunLike.congr_fun hp x)
  change p.val⁻¹ * e (j x) * (p.val⁻¹)⁻¹ = x.val
  rw [hx]
  group

end Subgroup
