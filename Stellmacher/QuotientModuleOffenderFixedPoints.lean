module

public import Stellmacher.QuotientModuleFixedPoints

/-!
# Witness independence of barred offender fixed centers

For two faithful quotient-module presentations of A/C_A(V) in a finite
ambient group, `QuotientModuleWitness.oneJ_fixedPoints_eq` identifies the
ambient images of C_V(J(V, S-bar)). Each presentation retains its own exact
action instance and acts on the original subgroup V. The exposed definition
`oneJFixedPoints` packages this ambient subgroup for downstream normality
statements; its body is exposed intentionally to connect to fixed-point APIs.

The common projection kernel gives an equivalence intertwining both
projections. Their conjugation equations make this equivalence equivariant.
Mapping subgroups then preserves fixed subgroups, subgroup orders, the
Section 1 measure, and elementary offender families. Applying this in both
directions identifies their generated joins and hence their fixed centers.

This is the presentation bridge for the barred fixed center in Stellmacher
(8.4), `refs/files/stellmacher-n-group.pdf`, journal p.38. It asserts neither
normality nor equality with the unbarred raw LocalJ fixed center, and needs
no numbered result of Sections 6--8.
-/

namespace Stellmacher.Later

universe u

private theorem fixed_map_equiv
    {X Y V : Type u} [Group X] [Group Y] [Group V]
    [MulDistribMulAction X V] [MulDistribMulAction Y V]
    (equiv : X ≃* Y) (compatible : ∀ actor (vector : V), equiv actor • vector = actor • vector)
    (sub : Subgroup X) :
    FixedPoints.subgroup (sub.map equiv.toMonoidHom) V = FixedPoints.subgroup sub V := by
  ext vector
  simp only [FixedPoints.mem_subgroup]
  constructor
  · intro fixed actor
    have heq := fixed ⟨equiv actor, Subgroup.mem_map_of_mem equiv.toMonoidHom actor.property⟩
    change equiv (actor : X) • vector = vector at heq
    rwa [compatible] at heq
  · intro fixed actor
    obtain ⟨preimage, hpreimage, heq⟩ := actor.property
    change (actor : Y) • vector = vector
    rw [← heq]
    change equiv preimage • vector = vector
    rw [compatible]
    exact fixed ⟨preimage, hpreimage⟩

private theorem oneA_map_equiv
    {X Y V : Type u} [Group X] [Group Y] [Group V] [Finite V]
    [MulDistribMulAction X V] [MulDistribMulAction Y V]
    (equiv : X ≃* Y) (compatible : ∀ actor (vector : V), equiv actor • vector = actor • vector)
    (sylow sub : Subgroup X) (hsub : SectionOne.oneA (V := V) sylow sub) :
    SectionOne.oneA (V := V) (sylow.map equiv.toMonoidHom) (sub.map equiv.toMonoidHom) := by
  have := hsub.2.1
  refine ⟨Subgroup.map_mono hsub.1, IsElementaryAbelian.map equiv.toMonoidHom, ?_⟩
  unfold SectionOne.m
  rw [fixed_map_equiv equiv compatible, Subgroup.card_map_of_injective equiv.injective]
  exact hsub.2.2

private theorem oneJ_map_le
    {X Y V : Type u} [Group X] [Group Y] [Group V] [Finite V]
    [MulDistribMulAction X V] [MulDistribMulAction Y V]
    (equiv : X ≃* Y) (compatible : ∀ actor (vector : V), equiv actor • vector = actor • vector)
    (sylow : Subgroup X) :
    (SectionOne.oneJ (V := V) sylow).map equiv.toMonoidHom ≤
      SectionOne.oneJ (V := V) (sylow.map equiv.toMonoidHom) := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro sub hsub
  apply Subgroup.map_le_iff_le_comap.mp
  exact le_sSup (oneA_map_equiv equiv compatible sylow sub hsub)

private theorem oneJ_map_equiv
    {X Y V : Type u} [Group X] [Group Y] [Group V] [Finite V]
    [MulDistribMulAction X V] [MulDistribMulAction Y V]
    (equiv : X ≃* Y) (compatible : ∀ actor (vector : V), equiv actor • vector = actor • vector)
    (sylow : Subgroup X) :
    (SectionOne.oneJ (V := V) sylow).map equiv.toMonoidHom =
      SectionOne.oneJ (V := V) (sylow.map equiv.toMonoidHom) := by
  apply le_antisymm (oneJ_map_le equiv compatible sylow)
  have reverse : ∀ actor (vector : V), equiv.symm actor • vector = actor • vector := by
    intro actor vector
    simpa using (compatible (equiv.symm actor) vector).symm
  have hrev := oneJ_map_le equiv.symm reverse (sylow.map equiv.toMonoidHom)
  apply (Subgroup.map_le_map_iff_of_injective
    (f := equiv.symm.toMonoidHom) equiv.symm.injective).mp
  simpa [Subgroup.map_map] using hrev

private theorem witness_equiv
    {G : Type u} [Group G] {A B V : Subgroup G}
    (first second : QuotientModuleWitness A B V) :
    let _ := first.groupX
    let _ := second.groupX
    ∃ equiv : first.X ≃* second.X,
      (∀ actor, equiv (first.projection actor) = second.projection actor) ∧
      ∀ actor vector, second.action (equiv actor) vector = first.action actor vector := by
  let := first.groupX
  let := second.groupX
  let left := QuotientGroup.liftEquiv first.projection.ker first.surjective rfl
  let right := QuotientGroup.liftEquiv first.projection.ker second.surjective
    (first.kernel_eq.trans second.kernel_eq.symm)
  let equiv := left.symm.trans right
  have projection : ∀ actor, equiv (first.projection actor) = second.projection actor := by
    intro actor
    change right (left.symm (first.projection actor)) = second.projection actor
    rw [← QuotientGroup.liftEquiv_mk first.projection.ker first.surjective rfl actor]
    change right (left.symm (left _)) = _
    rw [left.symm_apply_apply]
    rfl
  refine ⟨equiv, projection, ?_⟩
  intro actor vector
  obtain ⟨preimage, rfl⟩ := first.surjective actor
  rw [projection]
  apply Subtype.ext
  rw [second.action_compatible, first.action_compatible]

/-- The ambient fixed center of the offender join in this quotient presentation. -/
@[expose] public noncomputable def QuotientModuleWitness.oneJFixedPoints
    {G : Type u} [Group G] [Finite G] {A B V : Subgroup G}
    (witness : QuotientModuleWitness A B V) (S : Subgroup G) : Subgroup G :=
  let _ := witness.groupX
  let _ := MulDistribMulAction.compHom V witness.action
  (FixedPoints.subgroup
    (SectionOne.oneJ (V := V) ((S.subgroupOf A).map witness.projection)) V).map V.subtype

/-- Faithful presentations of the same local quotient have the same offender fixed center. -/
public theorem QuotientModuleWitness.oneJ_fixedPoints_eq
    {G : Type u} [Group G] [Finite G] {A V : Subgroup G}
    (first second : QuotientModuleWitness A (A ⊓ Subgroup.centralizer (V : Set G)) V)
    (S : Subgroup G) : first.oneJFixedPoints S = second.oneJFixedPoints S := by
  let := first.groupX
  let := second.groupX
  let := MulDistribMulAction.compHom V first.action
  let := MulDistribMulAction.compHom V second.action
  obtain ⟨equiv, projection, compatible⟩ := witness_equiv first second
  have hequiv : ∀ actor vector, equiv actor • vector = actor • vector := compatible
  have hprojection : equiv.toMonoidHom.comp first.projection = second.projection := by
    ext actor
    exact projection actor
  have hj := oneJ_map_equiv equiv hequiv ((S.subgroupOf A).map first.projection)
  rw [Subgroup.map_map, hprojection] at hj
  unfold QuotientModuleWitness.oneJFixedPoints
  dsimp only
  rw [← hj, fixed_map_equiv equiv hequiv]

end Stellmacher.Later
