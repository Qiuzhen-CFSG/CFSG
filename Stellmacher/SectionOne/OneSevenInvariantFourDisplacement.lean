module
public import Stellmacher.SectionOne.OneSevenConjugateCommonFixed

/-!
# Rank-one displacement in an invariant four-element subgroup

For two complementary canonical supports exchanged by a supplied actor, let a
rank-one actor belong to the first factor. A subgroup of order four preserved
by both actors contains the rank-one displacement. If the displacement were
not contained, its order two would make its intersection with that subgroup
trivial, so the rank-one actor would fix the subgroup pointwise. Invariance
under the exchanging actor gives the same conclusion for the conjugate actor.
Their common fixed subgroup has order four and contains their displacements;
cardinality forces equality with the supplied subgroup, a contradiction.

The exact original action, canonical factor, and exchanging actor are retained.
This is the action-theoretic ingredient for the center containment following
(9.9)(3), printed p.56/PDF p.46 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionOne
universe u

public theorem oneSevenFactor_displacement_le_invariant_four
    {W : Type u} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (X : Subgroup (MulAut W)) (hyp : Hypotheses X W)
    (D : Subgroup X) (hD : IsOneSevenFactor (V := W) D)
    (a c : X) (ha : a ∈ D)
    (hrank : Nat.card (commutatorAction (Subgroup.zpowers (a : MulAut W)) W) = 2)
    (hne : commutatorAction D W ≠
      (commutatorAction D W).map (c : MulAut W).toMonoidHom)
    (hspan : commutatorAction D W ⊔
      (commutatorAction D W).map (c : MulAut W).toMonoidHom = ⊤)
    (M : Subgroup W) (hMcard : Nat.card M = 4)
    (haM : ∀ w ∈ M, (a : MulAut W) w ∈ M)
    (hcM : M.map (c : MulAut W).toMonoidHom = M) :
    commutatorAction (Subgroup.zpowers (a : MulAut W)) W ≤ M := by
  let R := commutatorAction (Subgroup.zpowers (a : MulAut W)) W
  by_contra hnot
  change ¬ R ≤ M at hnot
  have hRM : R ⊓ M = ⊥ := by
    by_contra hneRM
    have hpositive := (Subgroup.one_lt_card_iff_ne_bot _).mpr hneRM
    have heq : R ⊓ M = R := Subgroup.eq_of_le_of_card_ge inf_le_left (by
      change Nat.card R=2 at hrank
      omega)
    exact hnot (heq ▸ inf_le_right)
  have hfixed (w : W) (hw : w∈M) : (a:MulAut W) w=w := by
    let delta := w⁻¹ * (a:MulAut W) w
    have hdR : delta∈R := by
      change delta∈commutatorAction (Subgroup.zpowers (a:MulAut W)) W
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨a,Subgroup.mem_zpowers (a:MulAut W)⟩,w,rfl⟩
    have hdM : delta∈M := M.mul_mem (M.inv_mem hw) (haM w hw)
    have heq : delta=1 := by
      have hh : delta∈R⊓M := ⟨hdR,hdM⟩
      rw [hRM,Subgroup.mem_bot] at hh
      exact hh
    exact (inv_mul_eq_one.mp heq).symm
  have hfirst : M ≤ FixedPoints.subgroup (Subgroup.zpowers (a:MulAut W)) W := by
    intro w hw mover
    exact smul_eq_self_of_mem_zpowers mover.property (hfixed w hw)
  have hsecond : M ≤ FixedPoints.subgroup
      (Subgroup.zpowers ((c*a*c⁻¹ : X):MulAut W)) W := by
    intro w hw mover
    have hcinv : (c:MulAut W).symm w∈M := by
      have hh : w∈M.map (c:MulAut W).toMonoidHom := hcM.symm ▸ hw
      exact Subgroup.mem_map_equiv.mp hh
    have hfix : ((c*a*c⁻¹:X):MulAut W) w=w := by
      change (c:MulAut W) ((a:MulAut W) ((c:MulAut W).symm w))=w
      rw [hfixed _ hcinv,MulEquiv.apply_symm_apply]
    exact smul_eq_self_of_mem_zpowers mover.property hfix
  obtain ⟨hfixedEq,hfixedCard,_⟩ := oneSevenFactor_conjugate_common_fixed
    X hyp D hD a c ha hrank hne hspan
  have heq : M = FixedPoints.subgroup (Subgroup.zpowers (a:MulAut W)) W ⊓
      FixedPoints.subgroup (Subgroup.zpowers ((c*a*c⁻¹:X):MulAut W)) W :=
    Subgroup.eq_of_le_of_card_ge (le_inf hfirst hsecond) (by rw [hfixedCard,hMcard])
  apply hnot
  rw [heq,hfixedEq]
  exact le_sup_left

end Stellmacher.SectionOne
