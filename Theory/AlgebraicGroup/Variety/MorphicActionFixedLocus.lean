module

public import Theory.AlgebraicGroup.Bor1.MorphicActionSchemeLaws
public import Theory.AlgebraicGroup.Variety.ClosedLocus

/-!
# The fixed locus of a normal subgroup

The common fixed points of a subgroup form a reduced closed subvariety.
For a normal subgroup, the ambient morphic action restricts to this locus:
normality gives invariance on rational points, and closed-point extensionality
gives the scheme identities needed to restrict the action morphism. The
locus is complete whenever the original variety is complete.

This is the fixed-locus induction step in Borel, *Linear Algebraic Groups*,
§10.4 (`refs/KGroup/Bor1/Chapter3.tex`).
-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
variable {X : Geometric k}

private theorem fixedLocus_morphism_ext_points
    {V W : Geometric k} (f g : Morphism V W)
    (h : ∀ x : Point V, f x = g x) : f = g := by
  letI : LocallyOfFiniteType (f.hom ≫ W.structureMap) := by
    rw [f.commutes]
    infer_instance
  apply Morphism.ext
  apply AlgebraicGeometry.ext_of_apply_eq W.structureMap
      (Set.univ : Set V.toScheme) isOpen_univ.isLocallyClosed dense_univ
  · intro z _ hz
    let p : Point V := ⟨pointOfClosedPoint V.structureMap z hz,
      pointOfClosedPoint_comp V.structureMap z hz⟩
    have hp : p.1 (IsLocalRing.closedPoint k) = z :=
      pointOfClosedPoint_apply V.structureMap z hz _
    have heq := congrArg (fun q : Point W => q.1 (IsLocalRing.closedPoint k)) (h p)
    change f.hom (p.1 (IsLocalRing.closedPoint k)) =
      g.hom (p.1 (IsLocalRing.closedPoint k)) at heq
    simpa only [hp] using heq
  · exact f.commutes.trans g.commutes.symm

namespace MorphicAction

/-- The reduced closed locus fixed by all rational points in a subgroup. -/
@[expose] public noncomputable def subgroupFixedLocus (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G)) : ClosedSubvariety X :=
  reducedFixedLocus fun n : N => A.translationMorphism n

/-- The inclusion identifies points of the fixed locus with exactly the
points fixed by the given subgroup. -/
public theorem point_mem_subgroupFixedLocus_iff (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G)) (x : Point X) :
    (∀ n : N, A.toMulAction.smul (n : Variety.Point G) x = x) ↔
      ∃! y : Point (A.subgroupFixedLocus N).toGeometric,
        (A.subgroupFixedLocus N).inclusion y = x := by
  constructor
  · intro hx
    apply (point_mem_reducedFixedLocus_iff (fun n : N => A.translationMorphism n) x).mp
    intro n
    exact (A.translationMorphism_apply n x).trans (hx n)
  · intro hx n
    have hf := (point_mem_reducedFixedLocus_iff
      (fun n : N => A.translationMorphism n) x).mpr hx
    exact (A.translationMorphism_apply n x).symm.trans (hf n)

private theorem subgroupFixedLocus_inclusion_injective (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G)) :
    Function.Injective (fun y : Point (A.subgroupFixedLocus N).toGeometric =>
      (A.subgroupFixedLocus N).inclusion y) := by
  intro y z hyz
  apply Subtype.ext
  apply (cancel_mono (A.subgroupFixedLocus N).inclusion.hom).mp
  exact congrArg Subtype.val hyz

/-- Every point of the fixed locus is fixed by the subgroup in the ambient variety. -/
public theorem subgroupFixedLocus_fixed (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G))
    (y : Point (A.subgroupFixedLocus N).toGeometric) (n : N) :
    A.toMulAction.smul (n : Variety.Point G) ((A.subgroupFixedLocus N).inclusion y) =
      (A.subgroupFixedLocus N).inclusion y := by
  apply (A.point_mem_subgroupFixedLocus_iff N _).mpr ?_ n
  exact ⟨y, rfl, fun z hz => A.subgroupFixedLocus_inclusion_injective N hz⟩

/-- A subgroup-fixed point makes the geometric fixed locus nonempty. -/
public theorem subgroupFixedLocus_nonempty (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G))
    (h : ∃ x : Point X, ∀ n : N, A.toMulAction.smul (n : Variety.Point G) x = x) :
    Nonempty (Point (A.subgroupFixedLocus N).toGeometric) := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, -, -⟩ := (A.point_mem_subgroupFixedLocus_iff N x).mp hx
  exact ⟨y⟩

/-- The fixed locus is complete as a closed subvariety. -/
public theorem subgroupFixedLocus_isComplete (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G)) (hX : IsComplete X) :
    IsComplete (A.subgroupFixedLocus N).toGeometric :=
  (A.subgroupFixedLocus N).isComplete hX

private theorem subgroup_fixed_smul (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G)) (hN : N.Normal)
    {x : Point X} (hx : ∀ n : N, A.toMulAction.smul (n : Variety.Point G) x = x)
    (g : Variety.Point G) (n : N) :
    A.toMulAction.smul (n : Variety.Point G) (A.toMulAction.smul g x) =
      A.toMulAction.smul g x := by
  letI := A.toMulAction
  have hn : g⁻¹ * (n : Variety.Point G) * g ∈ N := by
    simpa only [inv_inv] using hN.conj_mem n n.property g⁻¹
  have hfix := hx ⟨g⁻¹ * (n : Variety.Point G) * g, hn⟩
  change (n : Variety.Point G) • (g • x) = g • x
  calc
    (n : Variety.Point G) • (g • x) = g • ((g⁻¹ * (n : Variety.Point G) * g) • x) := by
      simp only [smul_smul, mul_assoc, mul_inv_cancel_left]
    _ = g • x := congrArg (g • ·) hfix

private noncomputable def fixedLocusAmbientAction (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G)) :
    Morphism (prod (ofAffine G) (A.subgroupFixedLocus N).toGeometric) X :=
  (Morphism.pair (fst _ _)
    ((snd _ _).comp (A.subgroupFixedLocus N).inclusion)).comp A.actionMorphism

private theorem fixedLocusAmbientAction_apply (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G)) (g : Variety.Point G)
    (y : Point (A.subgroupFixedLocus N).toGeometric) :
    A.fixedLocusAmbientAction N (prodPoint ((affinePointEquiv G).symm g) y) =
      A.toMulAction.smul g ((A.subgroupFixedLocus N).inclusion y) := by
  change A.actionMorphism
    (Morphism.pair (fst _ _) ((snd _ _).comp (A.subgroupFixedLocus N).inclusion)
      (prodPoint ((affinePointEquiv G).symm g) y)) = _
  rw [Morphism.pair_apply, fst_prodPoint, Morphism.comp_apply_point, snd_prodPoint]
  exact A.actionMorphism_apply g _

private theorem fixedLocusAmbientAction_equalizes (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G)) (hN : N.Normal) (n : N) :
    (A.fixedLocusAmbientAction N).comp (A.translationMorphism n) =
      (A.fixedLocusAmbientAction N).comp (Morphism.id X) := by
  apply fixedLocus_morphism_ext_points
  intro p
  obtain ⟨⟨g, y⟩, rfl⟩ := (prodPointEquiv (ofAffine G)
    (A.subgroupFixedLocus N).toGeometric).symm.surjective p
  change A.translationMorphism n (A.fixedLocusAmbientAction N (prodPoint g y)) =
    Morphism.id X (A.fixedLocusAmbientAction N (prodPoint g y))
  rw [← (affinePointEquiv G).symm_apply_apply g]
  rw [fixedLocusAmbientAction_apply, translationMorphism_apply, Morphism.id_apply_point]
  exact A.subgroup_fixed_smul N hN (A.subgroupFixedLocus_fixed N y)
    (affinePointEquiv G g) n

private noncomputable def fixedLocusActionMorphism (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G)) (hN : N.Normal) :
    Morphism (prod (ofAffine G) (A.subgroupFixedLocus N).toGeometric)
      (A.subgroupFixedLocus N).toGeometric :=
  restrictToReducedIntersection X
    (fun n : N => equalizerSupport (A.translationMorphism n) (Morphism.id X))
    (A.fixedLocusAmbientAction N) fun n =>
      range_subset_equalizerSupport_of_comp_eq _ _ _
        (A.fixedLocusAmbientAction_equalizes N hN n)

private theorem fixedLocusActionMorphism_apply (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G)) (hN : N.Normal) (g : Variety.Point G)
    (y : Point (A.subgroupFixedLocus N).toGeometric) :
    (A.subgroupFixedLocus N).inclusion
        (A.fixedLocusActionMorphism N hN (prodPoint ((affinePointEquiv G).symm g) y)) =
      A.toMulAction.smul g ((A.subgroupFixedLocus N).inclusion y) := by
  have h := restrictToReducedIntersection_inclusion X
    (fun n : N => equalizerSupport (A.translationMorphism n) (Morphism.id X))
    (A.fixedLocusAmbientAction N) (fun n =>
      range_subset_equalizerSupport_of_comp_eq _ _ _
        (A.fixedLocusAmbientAction_equalizes N hN n))
  have hp := congrArg (fun f => f (prodPoint ((affinePointEquiv G).symm g) y)) h
  exact hp.trans (A.fixedLocusAmbientAction_apply N g y)

/-- The ambient morphic action restricted to the fixed locus of a normal subgroup. -/
public noncomputable def onSubgroupFixedLocus (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G)) (hN : N.Normal) :
    MorphicAction G (A.subgroupFixedLocus N).toGeometric where
  smul g y := A.fixedLocusActionMorphism N hN (prodPoint ((affinePointEquiv G).symm g) y)
  one_smul y := by
    apply A.subgroupFixedLocus_inclusion_injective N
    exact (A.fixedLocusActionMorphism_apply N hN 1 y).trans (A.toMulAction.one_smul _)
  mul_smul g h y := by
    apply A.subgroupFixedLocus_inclusion_injective N
    exact (A.fixedLocusActionMorphism_apply N hN (g * h) y).trans
      ((A.toMulAction.mul_smul g h _).trans
        ((A.fixedLocusActionMorphism_apply N hN g _).trans
          (congrArg (A.toMulAction.smul g)
            (A.fixedLocusActionMorphism_apply N hN h y))).symm)
  actionMorphism := A.fixedLocusActionMorphism N hN
  actionMorphism_apply _ _ := rfl

/-- The inclusion of a normal-subgroup fixed locus is equivariant. -/
@[simp] public theorem onSubgroupFixedLocus_smul (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G)) (hN : N.Normal) (g : Variety.Point G)
    (y : Point (A.subgroupFixedLocus N).toGeometric) :
    (A.subgroupFixedLocus N).inclusion ((A.onSubgroupFixedLocus N hN).toMulAction.smul g y) =
      A.toMulAction.smul g ((A.subgroupFixedLocus N).inclusion y) :=
  A.fixedLocusActionMorphism_apply N hN g y

/-- The normal subgroup acts trivially on its fixed locus. -/
public theorem onSubgroupFixedLocus_subgroup_fixed (A : MorphicAction G X)
    (N : Subgroup (Variety.Point G)) (hN : N.Normal)
    (y : Point (A.subgroupFixedLocus N).toGeometric) (n : N) :
    (A.onSubgroupFixedLocus N hN).toMulAction.smul (n : Variety.Point G) y = y := by
  apply A.subgroupFixedLocus_inclusion_injective N
  exact (A.onSubgroupFixedLocus_smul N hN n y).trans (A.subgroupFixedLocus_fixed N y n)

end MorphicAction
end Theory.AlgebraicGroup.Variety.Geometric
