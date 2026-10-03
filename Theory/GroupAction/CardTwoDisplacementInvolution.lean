module
public import Theory.GroupAction.FourElementInvolutionLines
public import Theory.Comparator.Defs

/-!
# An order-two displacement detects an involution

An automorphism of a finite elementary abelian two-group is an involution
when its full cyclic-action displacement subgroup has order two. There is
no order assumption on the original automorphism.

The cyclic group preserves its displacement subgroup. Every automorphism
of that order-two subgroup is the identity, so the first displacement is
fixed. Expanding this identity in characteristic two shows that the square
of the original automorphism acts trivially. The nontrivial displacement
rules out the identity automorphism.

This is the elementary action calculation behind the transvection step in
Stellmacher (9.4), printed p.51 of `refs/files/stellmacher-n-group.pdf`.
It also applies independently of the graph and local group hypotheses.
-/

open scoped IsMulCommutative

private theorem displacement_card_two_fixed
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (actor : MulAut V)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers actor) V) = 2) :
    ∀ point ∈ commutatorAction (Subgroup.zpowers actor) V, actor point = point := by
  let D := commutatorAction (Subgroup.zpowers actor) V
  have hinvariant : IsInvariant (Subgroup.zpowers actor) V D := commutatorAction_isInvariant
  obtain ⟨line, _, hline⟩ := (Nat.card_eq_two_iff' (1 : D)).mp hcard
  intro point hpoint
  by_cases hone : point = 1
  · subst point
    exact map_one actor
  have hmove : actor point ∈ D :=
    (hinvariant.invariant ⟨actor, Subgroup.mem_zpowers actor⟩ point).mp hpoint
  have hpointEq : (⟨point, hpoint⟩ : D) = line :=
    hline ⟨point, hpoint⟩ (fun heq => hone (congrArg Subtype.val heq))
  have hmoveEq : (⟨actor point, hmove⟩ : D) = line :=
    hline ⟨actor point, hmove⟩ (fun heq =>
      hone (actor.injective ((congrArg Subtype.val heq).trans (map_one actor).symm)))
  exact congrArg Subtype.val (hmoveEq.trans hpointEq.symm)

public theorem isInvolution_of_card_two_displacement
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (actor : MulAut V)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers actor) V) = 2) :
    IsInvolution actor := by
  have hinv (point : V) : point⁻¹ = point := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) point
  have hsquare : actor ^ 2 = 1 := by
    ext point
    have hmem : point⁻¹ * actor point ∈ commutatorAction (Subgroup.zpowers actor) V :=
      Subgroup.subset_closure
        ⟨⟨actor, Subgroup.mem_zpowers actor⟩, point, Subgroup.mem_top point, rfl⟩
    have hfixed := displacement_card_two_fixed actor hcard _ hmem
    simp only [map_mul, hinv] at hfixed
    have heq : actor (actor point) = point := by
      apply mul_left_cancel (a := actor point)
      calc
        actor point * actor (actor point) = point * actor point := hfixed
        _ = actor point * point := mul_comm _ _
    exact heq
  refine ⟨?_, hsquare⟩
  intro hone
  have hbot : commutatorAction (Subgroup.zpowers actor) V = ⊥ := by
    apply bot_unique
    rw [commutatorAction_eq_closure, Subgroup.closure_le]
    rintro _ ⟨mover, point, rfl⟩
    have hmover : (mover : MulAut V) = 1 := by
      obtain ⟨power, hpower⟩ := mover.property
      simpa only [hone, one_zpow] using hpower.symm
    change point⁻¹ * (mover : MulAut V) point = 1
    rw [hmover]
    exact inv_mul_cancel point
  have hsize := Subgroup.card_eq_one.mpr hbot
  omega
