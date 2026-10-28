module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedSubgroups
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Roots
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup

/-!
# Root invariance for the supplied D4 graph-field geometry

The chosen root parametrizations are onto the actual root subgroups. The
published graph formula and surjectivity of squaring therefore give exact
images of those subgroups. Passing to generated subgroups proves invariance
of the positive and negative unipotents. Positivity is checked against the
existing enumeration of the actual standard D4 roots.

The point formula is graph first, then the nth ordinary Frobenius. All
statements hold for every exponent, including one. No ambient-generation or
fixed-generation conclusion is inferred from these invariance statements.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 11.2 and the setup of 11.1.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedRootTorus
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

private def frobeniusEnd (S : Geometry K) : Monoid.End (Variety.Point K) :=
  S.frobenius.onPoints

/-- The actual root permutation induced by the supplied graph automorphism. -/
def diagramRoot (S : Geometry K) : Equiv.Perm S.roots.Root :=
  S.rootIndex.trans (typeD4DiagramEquiv.indexEquiv.trans S.rootIndex.symm)

/-- The induced permutation has cube one on every realized root. -/
@[simp] theorem diagramRoot_three (S : Geometry K) (a : S.roots.Root) :
    diagramRoot S (diagramRoot S (diagramRoot S a)) = a := by
  simp [diagramRoot]

private theorem diagram_pos (r : TypeDRootIndex 4)
    (hr : (typeDRootPairing_base 2).IsPos r) :
    (typeDRootPairing_base 2).IsPos (typeD4DiagramEquiv.indexEquiv r) := by
  obtain ⟨i, rfl⟩ := (Set.ext_iff.mp Standard.PositiveCoordinates.range_rootIndex r).mpr hr
  rw [Standard.PositiveCoordinates.diagram_rootIndex]
  exact Standard.PositiveCoordinates.rootIndex_positive _

/-- The graph permutation preserves the supplied positive system exactly. -/
theorem diagramRoot_positive_iff (S : Geometry K) (a : S.roots.Root) :
    diagramRoot S a ∈ S.roots.positive ↔ a ∈ S.roots.positive := by
  have hp : ∀ b, b ∈ S.roots.positive → diagramRoot S b ∈ S.roots.positive := by
    intro b hb
    rw [S.positive] at hb ⊢
    simpa [diagramRoot] using diagram_pos (S.rootIndex b) hb
  exact ⟨fun h => by simpa using hp _ (hp _ h), hp a⟩

private theorem negative_iff (S : Geometry K) (a : S.roots.Root) :
    a ∈ S.roots.neg ⁻¹' S.roots.positive ↔ a ∉ S.roots.positive := by
  constructor
  · intro hn hp
    have h : a ∈ (∅ : Set S.roots.Root) :=
      S.bigCell.data.positive.1 ▸ (show a ∈ S.roots.positive ∩
        S.roots.neg ⁻¹' S.roots.positive from ⟨hp, hn⟩)
    exact h
  · intro hp
    have h : a ∈ S.roots.positive ∪ S.roots.neg ⁻¹' S.roots.positive := by
      rw [S.bigCell.data.positive.2.1]
      trivial
    exact h.resolve_left hp

/-- The same permutation preserves the opposite positive system. -/
theorem diagramRoot_negative_iff (S : Geometry K) (a : S.roots.Root) :
    diagramRoot S a ∈ S.roots.neg ⁻¹' S.roots.positive ↔
      a ∈ S.roots.neg ⁻¹' S.roots.positive := by
  rw [negative_iff, negative_iff, diagramRoot_positive_iff]

/-- The supplied root parametrization, included in the ambient point group. -/
def rootElement (S : Geometry K) (a : S.roots.Root) (t : k) : Variety.Point K :=
  (S.roots.rootSubgroup a).includePoint ((S.rootParameter a).value t)

/-- Every parametrized point belongs to its actual root subgroup. -/
theorem rootElement_mem (S : Geometry K) (a : S.roots.Root) (t : k) :
    rootElement S a t ∈ S.roots.rootSubgroup a :=
  ((S.roots.rootSubgroup a).pointEquiv ((S.rootParameter a).value t)).property

/-- The root parameters cover the entire actual root subgroup. -/
theorem mem_rootSubgroup_iff (S : Geometry K) (a : S.roots.Root) (g : Variety.Point K) :
    g ∈ S.roots.rootSubgroup a ↔ ∃ t, rootElement S a t = g := by
  constructor
  · intro hg
    let x := (S.roots.rootSubgroup a).pointEquiv.symm ⟨g, hg⟩
    let y := (S.rootParameter a).inv.onPoints x
    refine ⟨Multiplicative.toAdd (additiveGroupPointEquiv k y), ?_⟩
    have hy : kPlusPoint (Multiplicative.toAdd (additiveGroupPointEquiv k y)) = y := by
      apply (additiveGroupPointEquiv k).injective
      rfl
    change (S.roots.rootSubgroup a).includePoint
      ((S.rootParameter a).hom.onPoints (kPlusPoint _)) = g
    rw [hy]
    change (S.roots.rootSubgroup a).includePoint
      ((S.rootParameter a).hom.onPoints ((S.rootParameter a).inv.onPoints x)) = g
    rw [(S.rootParameter a).inv_hom_id]
    exact congrArg Subtype.val ((S.roots.rootSubgroup a).pointEquiv.apply_symm_apply ⟨g, hg⟩)
  · rintro ⟨t, rfl⟩
    exact rootElement_mem S a t

/-- The graph map permutes root labels without changing the parameter. -/
theorem diagram_rootElement (S : Geometry K) (a : S.roots.Root) (t : k) :
    S.diagram.toMulEquiv (rootElement S a t) = rootElement S (diagramRoot S a) t :=
  S.diagram_root a t

/-- Ordinary Frobenius squares the parameter in each root subgroup. -/
theorem frobenius_rootElement (S : Geometry K) (a : S.roots.Root) (t : k) :
    S.frobenius.onPoints (rootElement S a t) = rootElement S a (t ^ 2) :=
  S.frobenius_root a t

private theorem frobenius_pow_rootElement (S : Geometry K) (n : ℕ) (a : S.roots.Root) (t : k) :
    (frobeniusEnd S ^ n) (rootElement S a t) =
      rootElement S a (t ^ (2 ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change S.frobenius.onPoints ((frobeniusEnd S ^ n) (rootElement S a t)) = _
    rw [ih, frobenius_rootElement, ← pow_mul, Nat.pow_succ]

/-- Graph followed by the nth ordinary Frobenius has exponent `2 ^ n`. -/
theorem graphFieldEnd_rootElement (S : Geometry K) (n : ℕ) (a : S.roots.Root) (t : k) :
    graphFieldEnd S n (rootElement S a t) =
      rootElement S (diagramRoot S a) (t ^ (2 ^ n)) := by
  change (frobeniusEnd S ^ n) (S.diagram.toMulEquiv (rootElement S a t)) = _
  rw [diagram_rootElement, frobenius_pow_rootElement]

/-- The graph map sends each entire root subgroup onto the indicated one. -/
theorem diagram_map_rootSubgroup (S : Geometry K) (a : S.roots.Root) :
    (S.roots.rootSubgroup a).toSubgroup.map S.diagram.toMulEquiv.toMonoidHom =
      (S.roots.rootSubgroup (diagramRoot S a)).toSubgroup := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨t, rfl⟩ := (mem_rootSubgroup_iff S a g).mp hg
    change S.diagram.toMulEquiv (rootElement S a t) ∈ _
    rw [diagram_rootElement]
    exact rootElement_mem S _ _
  · intro g hg
    obtain ⟨t, rfl⟩ := (mem_rootSubgroup_iff S _ g).mp hg
    exact ⟨rootElement S a t, rootElement_mem S a t, diagram_rootElement S a t⟩

variable [IsAlgClosed k]

/-- Squaring is surjective over the algebraically closed field, so the
ordinary Frobenius preserves each entire root subgroup. -/
theorem frobenius_map_rootSubgroup (S : Geometry K) (a : S.roots.Root) :
    (S.roots.rootSubgroup a).toSubgroup.map S.frobenius.onPoints =
      (S.roots.rootSubgroup a).toSubgroup := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨t, rfl⟩ := (mem_rootSubgroup_iff S a g).mp hg
    rw [frobenius_rootElement]
    exact rootElement_mem S _ _
  · intro g hg
    obtain ⟨t, rfl⟩ := (mem_rootSubgroup_iff S a g).mp hg
    obtain ⟨s, rfl⟩ := IsAlgClosed.exists_pow_nat_eq t (by decide : 0 < 2)
    exact ⟨rootElement S a s, rootElement_mem S a s, frobenius_rootElement S a s⟩

omit [IsAlgClosed k] in
private theorem map_rootGenerated (S : Geometry K)
    (f : Variety.Point K →* Variety.Point K) (e : Equiv.Perm S.roots.Root)
    (hf : ∀ a, (S.roots.rootSubgroup a).toSubgroup.map f =
      (S.roots.rootSubgroup (e a)).toSubgroup) (A : Set S.roots.Root) :
    (RootSubgroupGenerated S.roots A).map f = RootSubgroupGenerated S.roots (e '' A) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, RootSubgroupGenerated_le_iff]
    intro a ha g hg
    apply rootSubgroup_le_RootSubgroupGenerated S.roots
      (A := e '' A) (α := e a) ⟨a, ha, rfl⟩
    rw [← hf a]
    exact ⟨g, hg, rfl⟩
  · rw [RootSubgroupGenerated_le_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← hf]
    exact Subgroup.map_mono (rootSubgroup_le_RootSubgroupGenerated S.roots ha)

omit [IsAlgClosed k] in
/-- Graph equivariance extends from root subgroups to any generated root set. -/
theorem diagram_map_rootGenerated (S : Geometry K) (A : Set S.roots.Root) :
    (RootSubgroupGenerated S.roots A).map S.diagram.toMulEquiv.toMonoidHom =
      RootSubgroupGenerated S.roots (diagramRoot S '' A) :=
  map_rootGenerated S _ _ (diagram_map_rootSubgroup S) A

/-- Ordinary Frobenius preserves the subgroup generated by any set of roots. -/
theorem frobenius_map_rootGenerated (S : Geometry K) (A : Set S.roots.Root) :
    (RootSubgroupGenerated S.roots A).map S.frobenius.onPoints =
      RootSubgroupGenerated S.roots A := by
  simpa using map_rootGenerated S _ (Equiv.refl _) (frobenius_map_rootSubgroup S) A

private theorem frobenius_pow_map_rootGenerated (S : Geometry K) (n : ℕ) (A : Set S.roots.Root) :
    (RootSubgroupGenerated S.roots A).map (frobeniusEnd S ^ n) =
      RootSubgroupGenerated S.roots A := by
  induction n with
  | zero => exact Subgroup.map_id _
  | succ n ih =>
    rw [pow_succ']
    exact (Subgroup.map_map (RootSubgroupGenerated S.roots A)
      S.frobenius.onPoints (frobeniusEnd S ^ n)).symm.trans
        ((congrArg (Subgroup.map S.frobenius.onPoints) ih).trans
          (frobenius_map_rootGenerated S A))

/-- The graph-field image of a root-generated subgroup is given by
the image of its root set under the actual diagram permutation. -/
theorem graphFieldEnd_map_rootGenerated (S : Geometry K) (n : ℕ) (A : Set S.roots.Root) :
    (RootSubgroupGenerated S.roots A).map (graphFieldEnd S n) =
      RootSubgroupGenerated S.roots (diagramRoot S '' A) := by
  exact (Subgroup.map_map (RootSubgroupGenerated S.roots A)
    (frobeniusEnd S ^ n) S.diagram.toMulEquiv.toMonoidHom).symm.trans
      ((congrArg (Subgroup.map (frobeniusEnd S ^ n))
        (diagram_map_rootGenerated S A)).trans
          (frobenius_pow_map_rootGenerated S n _))

omit [IsAlgClosed k] in
private theorem diagramRoot_image_eq (S : Geometry K) (A : Set S.roots.Root)
    (hA : ∀ a, diagramRoot S a ∈ A ↔ a ∈ A) : diagramRoot S '' A = A := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (hA b).mpr hb
  · intro ha
    exact ⟨(diagramRoot S).symm a, (hA _).mp (by simpa), by simp⟩

/-- The actual positive unipotent subgroup is graph-field invariant. -/
theorem graphFieldEnd_map_positive (S : Geometry K) (n : ℕ) :
    (RootSubgroupGenerated S.roots S.roots.positive).map (graphFieldEnd S n) =
      RootSubgroupGenerated S.roots S.roots.positive := by
  rw [graphFieldEnd_map_rootGenerated,
    diagramRoot_image_eq S _ (diagramRoot_positive_iff S)]

/-- The actual negative unipotent subgroup is graph-field invariant. -/
theorem graphFieldEnd_map_negative (S : Geometry K) (n : ℕ) :
    (RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive)).map
      (graphFieldEnd S n) =
      RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive) := by
  rw [graphFieldEnd_map_rootGenerated,
    diagramRoot_image_eq S _ (diagramRoot_negative_iff S)]

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedRootTorus
