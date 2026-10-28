module
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Comparing perfect central covers over the original base

A cover attaining the universal kernel upper bound receives a bijective
universal lift: the order formula and surjectivity prove injectivity.
Comparing two such lifts gives an isomorphism commuting with both original
projections, in arbitrary universes. This retains the marked subgroup images
needed when transporting a local configuration into a concrete double cover.

Source: the universal-cover convention in Aschbacher--Smith I.1.1, p.407.
The concrete applications are the HS and Ru cases of 12.6.12, pp.825--826.
-/

public section
namespace PerfectCentralCovering
open Subgroup

private theorem card_eq_kernel_mul
    {E B : Type*} [Group E] [Group B] (f : E →* B)
    (hf : Function.Surjective f) : Nat.card E = Nat.card f.ker * Nat.card B := by
  have h := f.ker.card_mul_index
  rw [index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at h
  exact h.symm

/-- Covers attaining the universal kernel bound are isomorphic over their
original base. The conclusion retains the commuting triangle. -/
theorem Cover.exists_mulEquiv_over_of_kernel_bound
    {B E F : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    [Group E] [Finite E] [Group F] [Finite F]
    (f : Cover E B) (g : Cover F B)
    (hf : Nat.card (universalProjection B).ker ≤ Nat.card f.toMonoidHom.ker)
    (hg : Nat.card (universalProjection B).ker ≤ Nat.card g.toMonoidHom.ker) :
    ∃ e : E ≃* F, ∀ x, g.toMonoidHom (e x) = f.toMonoidHom x := by
  let := f.isPerfect
  let := g.isPerfect
  obtain ⟨a,ha,_⟩ := universalProjection_existsUnique_lift
    f.toMonoidHom f.surjective f.ker_le_center
  obtain ⟨b,hb,_⟩ := universalProjection_existsUnique_lift
    g.toMonoidHom g.surjective g.ker_le_center
  have has : Function.Surjective a :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      f.toMonoidHom a (ha ▸ universalProjection_surjective B) f.ker_le_center
  have hbs : Function.Surjective b :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      g.toMonoidHom b (hb ▸ universalProjection_surjective B) g.ker_le_center
  have hE : Nat.card (UniversalGroup B) ≤ Nat.card E := by
    rw [card_eq_kernel_mul (universalProjection B) (universalProjection_surjective B),
      card_eq_kernel_mul f.toMonoidHom f.surjective]
    exact Nat.mul_le_mul_right _ hf
  have hF : Nat.card (UniversalGroup B) ≤ Nat.card F := by
    rw [card_eq_kernel_mul (universalProjection B) (universalProjection_surjective B),
      card_eq_kernel_mul g.toMonoidHom g.surjective]
    exact Nat.mul_le_mul_right _ hg
  let ea := MulEquiv.ofBijective a (has.bijective_of_nat_card_le hE)
  let eb := MulEquiv.ofBijective b (hbs.bijective_of_nat_card_le hF)
  refine ⟨ea.symm.trans eb,fun x => ?_⟩
  change g.toMonoidHom (b (ea.symm x)) = f.toMonoidHom x
  exact (DFunLike.congr_fun hb (ea.symm x)).trans
    ((DFunLike.congr_fun ha (ea.symm x)).symm.trans
      (congrArg f.toMonoidHom (ea.apply_symm_apply x)))

end PerfectCentralCovering
