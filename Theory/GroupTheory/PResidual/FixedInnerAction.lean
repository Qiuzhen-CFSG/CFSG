module

public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.PPerfectHom

/-!
# Perfect actions commuting with an automorphism

A p-perfect actor has trivial image in a p-group outer quotient. For a
centerless group its inner action lifts uniquely to a group homomorphism.
Commutation with the marked automorphism puts this lift in its fixed subgroup;
if that subgroup is a p-group, the action is trivial.

Source application: Aschbacher--Smith, the PSL₂(p) case of the proof of
15.2.15, printed p.1118, refs/quasithin.pdf.
-/

public section
open Subgroup

namespace Theory.GroupTheory
variable {A L : Type*} [Group A] [Group L] {p : ℕ} [Fact p.Prime]

/-- A p-perfect automorphism action commuting with a has trivial image when
both its outer quotient and the fixed subgroup of a are p-groups. -/
theorem perfect_action_eq_one_of_fixed_and_outer_pGroups
    (hp : IsPPerfect p A) (hz : center L = ⊥)
    (ho : IsPGroup p (MulAut.Outer L)) (a : MulAut L)
    (ha : IsPGroup p a.fixedSubgroup) (f : A →* MulAut L)
    (hc : ∀ x, a * f x = f x * a) : f = 1 := by
  let e : L ≃* MulAut.innerSubgroup L :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hz)
  have hi (x : A) : f x ∈ MulAut.innerSubgroup L := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact DFunLike.congr_fun
      (hp.hom_eq_one_of_isPGroup ho ((QuotientGroup.mk' _).comp f)) x
  let g : A →* L := e.symm.toMonoidHom.comp (f.codRestrict _ hi)
  have hg (x : A) : MulAut.conj (g x) = f x :=
    congrArg Subtype.val (e.apply_symm_apply ⟨f x, hi x⟩)
  have hfix (x : A) : g x ∈ a.fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    apply MulAut.conj_injective_of_center_eq_bot hz
    have he : MulAut.conj (a (g x)) = a * MulAut.conj (g x) * a⁻¹ := by
      ext y
      simp
    rw [he, hg, hc, mul_assoc, mul_inv_cancel, mul_one]
  have htriv := hp.hom_eq_one_of_isPGroup ha (g.codRestrict _ hfix)
  ext x
  have hx : g x = 1 := congrArg Subtype.val (DFunLike.congr_fun htriv x)
  rw [← hg, hx, map_one]
  rfl
end Theory.GroupTheory
