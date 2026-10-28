module

public import Stellmacher.QuotientModuleOffenderFixedPoints
public import Stellmacher.QuotientModuleWitness

/-!
# Injective transport of quotient-module offender fixed points

An embedding transports a faithful quotient-module witness by retaining its
quotient group and conjugating its automorphism action through the equivalence
between the original module and its image. The projection is precomposed with
the inverse equivalence on the acting subgroup.

Equivariance identifies fixed subgroups and their cardinalities, so the genuine
Section 1 measure, offender family, and offender join are preserved. The resulting
ambient fixed subgroup is exactly the image of the original fixed subgroup.
No containment hypothesis on the subgroup whose image generates the offenders
is needed: `subgroupOf` already restricts it to the acting subgroup.
-/

namespace Stellmacher.Later

universe u

private theorem fixed_module_equiv
    {X V W : Type u} [Group X] [Group V] [Group W]
    [MulDistribMulAction X V] [MulDistribMulAction X W]
    (equiv : V ≃* W) (compatible : ∀ (actor : X) (vector : V),
      equiv (actor • vector) = actor • equiv vector)
    (sub : Subgroup X) :
    (FixedPoints.subgroup sub V).map equiv.toMonoidHom = FixedPoints.subgroup sub W := by
  ext vector
  constructor
  · rintro ⟨preimage, hpreimage, rfl⟩
    change ∀ actor : sub, (actor : X) • preimage = preimage at hpreimage
    change ∀ actor : sub, (actor : X) • equiv preimage = equiv preimage
    intro actor
    rw [← compatible, hpreimage actor]
  · intro hvector
    refine ⟨equiv.symm vector, ?_, equiv.apply_symm_apply vector⟩
    change ∀ actor : sub, (actor : X) • vector = vector at hvector
    change ∀ actor : sub, (actor : X) • equiv.symm vector = equiv.symm vector
    intro actor
    apply equiv.injective
    rw [compatible, equiv.apply_symm_apply, hvector actor]

private theorem oneJ_module_equiv
    {X V W : Type u} [Group X] [Group V] [Group W] [Finite V] [Finite W]
    [MulDistribMulAction X V] [MulDistribMulAction X W]
    (equiv : V ≃* W) (compatible : ∀ (actor : X) (vector : V),
      equiv (actor • vector) = actor • equiv vector)
    (sub : Subgroup X) :
    SectionOne.oneJ (V := V) sub = SectionOne.oneJ (V := W) sub := by
  have hcard : Nat.card V = Nat.card W := Nat.card_congr equiv.toEquiv
  have hfixed (actor : Subgroup X) :
      Nat.card (FixedPoints.subgroup actor V) = Nat.card (FixedPoints.subgroup actor W) := by
    rw [← fixed_module_equiv equiv compatible actor,
      Subgroup.card_map_of_injective equiv.injective]
  unfold SectionOne.oneJ SectionOne.oneA SectionOne.m
  simp only [hcard, hfixed]

private theorem centralizer_map_iff
    {G H : Type u} [Group G] [Group H] (embedding : G →* H)
    (injective : Function.Injective embedding) (V : Subgroup G) (actor : G) :
    embedding actor ∈ Subgroup.centralizer (V.map embedding : Set H) ↔
      actor ∈ Subgroup.centralizer (V : Set G) := by
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro h vector hvector
    apply injective
    simpa only [map_mul] using h (embedding vector) (Subgroup.mem_map_of_mem embedding hvector)
  · intro h vector hvector
    obtain ⟨preimage, hpreimage, rfl⟩ := hvector
    simpa only [map_mul] using congrArg embedding (h preimage hpreimage)

private theorem subgroupOf_map_equiv
    {G H : Type u} [Group G] [Group H] (embedding : G →* H)
    (injective : Function.Injective embedding) (A T : Subgroup G) :
    (T.subgroupOf A).map (A.equivMapOfInjective embedding injective).toMonoidHom =
      (T.map embedding).subgroupOf (A.map embedding) := by
  let equiv := A.equivMapOfInjective embedding injective
  ext actor
  obtain ⟨preimage, rfl⟩ := equiv.surjective actor
  constructor
  · rintro ⟨original, horiginal, heq⟩
    have heq' : original = preimage := equiv.injective heq
    subst original
    exact Subgroup.mem_map_of_mem embedding horiginal
  · intro hactor
    obtain ⟨original, horiginal, heq⟩ := hactor
    have heq' : original = (preimage : G) := injective heq
    refine ⟨preimage, ?_, rfl⟩
    change (preimage : G) ∈ T
    exact heq' ▸ horiginal

private noncomputable def mapWitness
    {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    (embedding : G →* H) (injective : Function.Injective embedding)
    {A V : Subgroup G}
    (w : QuotientModuleWitness A (A ⊓ Subgroup.centralizer (V : Set G)) V) :
    QuotientModuleWitness (A.map embedding)
      (A.map embedding ⊓ Subgroup.centralizer (V.map embedding : Set H)) (V.map embedding) := by
  let := w.groupX
  let := w.finiteX
  let actorEquiv := A.equivMapOfInjective embedding injective
  let vectorEquiv := V.equivMapOfInjective embedding injective
  let projection := w.projection.comp actorEquiv.symm.toMonoidHom
  let action := (MulAut.congr vectorEquiv).toMonoidHom.comp w.action
  refine {
    X := w.X
    projection := projection
    surjective := w.surjective.comp actorEquiv.symm.surjective
    kernel_eq := ?_
    module_le := Subgroup.map_mono w.module_le
    action := action
    action_compatible := ?_ }
  · ext actor
    obtain ⟨preimage, rfl⟩ := actorEquiv.surjective actor
    change w.projection (actorEquiv.symm (actorEquiv preimage)) = 1 ↔ _
    rw [actorEquiv.symm_apply_apply]
    change preimage ∈ w.projection.ker ↔ _
    rw [w.kernel_eq]
    change ((preimage : G) ∈ A ∧ (preimage : G) ∈ Subgroup.centralizer (V : Set G)) ↔
      (embedding (preimage : G) ∈ A.map embedding ∧
        embedding (preimage : G) ∈ Subgroup.centralizer (V.map embedding : Set H))
    rw [centralizer_map_iff embedding injective]
    simp only [preimage.property, Subgroup.mem_map_of_mem embedding preimage.property, true_and]
  · intro actor vector
    obtain ⟨preimage, rfl⟩ := actorEquiv.surjective actor
    obtain ⟨original, rfl⟩ := vectorEquiv.surjective vector
    change embedding ((w.action (w.projection (actorEquiv.symm (actorEquiv preimage))))
      (vectorEquiv.symm (vectorEquiv original)) : G) = _
    rw [actorEquiv.symm_apply_apply, vectorEquiv.symm_apply_apply, w.action_compatible]
    simp only [map_mul, map_inv]
    rfl

/-- An embedding preserves a faithful witness's genuine offender fixed subgroup. -/
public theorem quotientModuleWitness_exists_map_fixed
    {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    (embedding : G →* H) (injective : Function.Injective embedding)
    (A V T : Subgroup G)
    (w : QuotientModuleWitness A (A ⊓ Subgroup.centralizer (V : Set G)) V) :
    ∃ wH : QuotientModuleWitness (A.map embedding)
      (A.map embedding ⊓ Subgroup.centralizer (V.map embedding : Set H)) (V.map embedding),
      wH.oneJFixedPoints (T.map embedding) = (w.oneJFixedPoints T).map embedding := by
  let := w.groupX
  let wH := mapWitness embedding injective w
  let := wH.groupX
  let := MulDistribMulAction.compHom V w.action
  let : MulDistribMulAction w.X (V.map embedding) :=
    MulDistribMulAction.compHom (V.map embedding) wH.action
  let actorEquiv := A.equivMapOfInjective embedding injective
  let vectorEquiv := V.equivMapOfInjective embedding injective
  have compatible (actor : w.X) (vector : V) :
      vectorEquiv (actor • vector) = actor • vectorEquiv vector := by
    change vectorEquiv (w.action actor vector) =
      vectorEquiv (w.action actor (vectorEquiv.symm (vectorEquiv vector)))
    rw [vectorEquiv.symm_apply_apply]
  have hprojection :
      ((T.map embedding).subgroupOf (A.map embedding)).map wH.projection =
        (T.subgroupOf A).map w.projection := by
    rw [← subgroupOf_map_equiv embedding injective A T, Subgroup.map_map]
    congr 1
    ext actor
    change w.projection (actorEquiv.symm (actorEquiv actor)) = w.projection actor
    rw [actorEquiv.symm_apply_apply]
  refine ⟨wH, ?_⟩
  unfold QuotientModuleWitness.oneJFixedPoints
  dsimp only
  change (FixedPoints.subgroup
    (SectionOne.oneJ (G := w.X) (V := V.map embedding)
      (((T.map embedding).subgroupOf (A.map embedding)).map
        (w.projection.comp actorEquiv.symm.toMonoidHom))) (V.map embedding)).map
      (V.map embedding).subtype = _
  change ((T.map embedding).subgroupOf (A.map embedding)).map
    (w.projection.comp actorEquiv.symm.toMonoidHom) = _ at hprojection
  rw [hprojection, ← oneJ_module_equiv vectorEquiv compatible,
    ← fixed_module_equiv vectorEquiv compatible, Subgroup.map_map, Subgroup.map_map]
  rfl

end Stellmacher.Later
