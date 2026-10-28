module
public import Stellmacher.SectionOne.OneSevenTransvectionSupportSelection
public import Theory.GroupAction.ComplementaryFourSupportFixed
public import Theory.GroupAction.ActorSubtypeCommutator

/-!
# Common fixed points for conjugate canonical factors

For a canonical Section One factor acting on an elementary abelian two-module,
a cyclic actor of displacement rank one and its conjugate actor have exact
common fixed subgroup once the factor supports are distinct and span the
module. Distinct one-seven factors have disjoint supports and fix one another's
supports. The independent complementary-support cardinality theorem then
identifies the common fixed subgroup with the join of the two displacement
lines and gives order four.

This is the action-theoretic package used in Stellmacher (9.5), Journal of
Algebra 190 (1997), printed pp.52--53. It retains the actual subgroup `X` of
`MulAut W` and its supplied Section One action hypotheses.
-/

namespace Stellmacher.SectionOne
universe u
private theorem cyclic_actor_support_le
    {W : Type u} [Group W] (X : Subgroup (MulAut W))
    (D : Subgroup X) (a : X) (ha : a ∈ D) :
    commutatorAction (Subgroup.zpowers (a : MulAut W)) W ≤ commutatorAction D W := by
  rw [commutatorAction_eq_closure, Subgroup.closure_le]
  rintro point ⟨mover, vector, rfl⟩
  obtain ⟨power, hpower⟩ := mover.property
  refine Subgroup.subset_closure ⟨⟨a ^ power, D.zpow_mem ha power⟩, vector, Subgroup.mem_top vector, ?_⟩
  change vector⁻¹ * (mover : MulAut W) vector = vector⁻¹ * ((a ^ power : X) : MulAut W) vector
  rw [← hpower]
  rfl

public theorem oneSevenFactor_conjugate_common_fixed
    {W : Type u} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (X : Subgroup (MulAut W)) (hyp : Hypotheses X W)
    (D : Subgroup X) (hD : IsOneSevenFactor (V := W) D)
    (a c : X) (ha : a ∈ D)
    (hrank : Nat.card (commutatorAction (Subgroup.zpowers (a : MulAut W)) W) = 2)
    (hne : commutatorAction D W ≠
      (commutatorAction D W).map (c : MulAut W).toMonoidHom)
    (hspan : commutatorAction D W ⊔
      (commutatorAction D W).map (c : MulAut W).toMonoidHom = ⊤) :
    FixedPoints.subgroup (Subgroup.zpowers (a : MulAut W)) W ⊓
        FixedPoints.subgroup (Subgroup.zpowers ((c * a * c⁻¹ : X) : MulAut W)) W =
      commutatorAction (Subgroup.zpowers (a : MulAut W)) W ⊔
        commutatorAction (Subgroup.zpowers ((c * a * c⁻¹ : X) : MulAut W)) W ∧
    Nat.card (FixedPoints.subgroup (Subgroup.zpowers (a : MulAut W)) W ⊓
      FixedPoints.subgroup (Subgroup.zpowers ((c * a * c⁻¹ : X) : MulAut W)) W :
        Subgroup W) = 4 ∧
    Nat.card (commutatorAction (Subgroup.zpowers (a : MulAut W)) W ⊔
      commutatorAction (Subgroup.zpowers ((c * a * c⁻¹ : X) : MulAut W)) W :
        Subgroup W) = 4 := by
  let E := D.conjBy c
  let A := commutatorAction D W
  let B := commutatorAction E W
  let b : X := c * a * c⁻¹
  have hE : IsOneSevenFactor (V := W) E := hD.conjBy D c
  have hB : (commutatorAction D W).map (c : MulAut W).toMonoidHom = B :=
    RankOneThreeGroupAssembly.commutatorAction_conjBy D c
  have hDE : D ≠ E := by
    intro heq
    exact hne ((congrArg (fun K : Subgroup X => commutatorAction K W) heq).trans hB.symm)
  have hcompl : IsCompl A B := by
    refine ⟨oneSevenFactor_support_disjoint_of_ne hyp D E hD hE hDE, ?_⟩
    apply codisjoint_iff.mpr
    simpa only [hB] using hspan
  have hb : b ∈ E := ⟨a, ha, rfl⟩
  have hconj : (Subgroup.zpowers a).conjBy c = Subgroup.zpowers b := by
    change (Subgroup.zpowers a).map (MulAut.conj c).toMonoidHom = Subgroup.zpowers b
    rw [MonoidHom.map_zpowers]
    rfl
  have hcyclic (x : X) :
      commutatorAction (Subgroup.zpowers (x : MulAut W)) W =
        commutatorAction (Subgroup.zpowers x) W := by
    rw [← commutatorAction_map_actor_subtype X (Subgroup.zpowers x), MonoidHom.map_zpowers]
    rfl
  have hbrank : Nat.card (commutatorAction (Subgroup.zpowers (b : MulAut W)) W) = 2 := by
    rw [hcyclic, ← hconj, ← RankOneThreeGroupAssembly.commutatorAction_conjBy,
      Subgroup.card_map_of_injective
        (f := (MulDistribMulAction.toMulAut X W c).toMonoidHom)
        (MulDistribMulAction.toMulAut X W c).injective,
      ← hcyclic]
    exact hrank
  have haB : ∀ x ∈ B, (a : MulAut W) x = x := by
    intro x hx
    exact (oneSevenFactor_commutatorAction_le_fixedPoints hyp D E hD hE hDE hx) ⟨a, ha⟩
  have hbA : ∀ x ∈ A, (b : MulAut W) x = x := by
    intro x hx
    exact (oneSevenFactor_commutatorAction_le_fixedPoints hyp E D hE hD hDE.symm hx) ⟨b, hb⟩
  exact MulAut.complementary_four_support_common_fixed A B hcompl hD.2.2.1 hE.2.2.1
    (a : MulAut W) (b : MulAut W) hrank hbrank
    (cyclic_actor_support_le X D a ha) (cyclic_actor_support_le X E b hb) haB hbA


end Stellmacher.SectionOne
