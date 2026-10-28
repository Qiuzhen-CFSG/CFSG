module
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.Inputs
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.NormalizerActionExistence.Action
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.NormalizerActionExistence.Reflections

/-!
The normalizer-root-action existence proof, reduced to independent source geometry.

The action and reflection permutations are constructed from the supplied realized
root data in the two imported modules. Here a chamber-stabilizer theorem gives
the torus kernel. Transitivity of reflection words on positive systems then
reduces each normalizer element to that stabilizer, proving that the image is
exactly the fundamental reflection group. This works also when the root set is
empty; no root is chosen in the argument.

The theorem below is a conditional assembly, not the unconditional source theorem.
Same-weight uniqueness, the chamber stabilizer, realization of simple reflections,
and the two positive-system facts remain explicit. Their reductive geometric
producers must be supplied before claiming GLS3, 1.9.5(f) or Borel 14.15 T2.
-/

universe u
namespace Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.NormalizerActionExistence
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
variable {D : RootGroupData G T} (hD : D.IsRealization) {P : Set D.Root}

omit [IsAlgClosed k] in
/-- A trivial positive-chamber stabilizer modulo the torus gives the exact
relative kernel. -/
public theorem kernel_eq_of_chamber_stabilizer (hT : IsSubtorus T)
    (hstabilizer : ∀ n : T.normalizer.toSubgroup,
      (∀ α, rootAction hD n α ∈ P ↔ α ∈ P) → n.val ∈ T.toSubgroup) :
    (rootAction hD).ker = T.toSubgroup.subgroupOf T.normalizer.toSubgroup := by
  apply le_antisymm _ (torus_le_kernel hD hT)
  intro n hn
  apply hstabilizer n
  intro α
  change rootAction hD n = 1 at hn
  rw [hn]
  rfl

/-- Reduction to the positive chamber eliminates all extra normalizer actions,
including possible diagram automorphisms of the abstract root system. -/
public theorem range_eq_of_chamber_reduction (hT : IsSubtorus T)
    (hadd : D.IsRootAdditionComplete) (hP : IsPositiveSystem D P)
    (hstabilizer : ∀ n : T.normalizer.toSubgroup,
      (∀ α, rootAction hD n α ∈ P ↔ α ∈ P) → n.val ∈ T.toSubgroup)
    (hreflection : ∀ i : {α // α ∈ FundamentalRootsFor D P},
      reflectionPerm hD i.val ∈ (rootAction hD).range)
    (hchambers : ∀ Q : Set D.Root, IsPositiveSystem D Q →
      ∃ w ∈ reflectionGroup hD P, ∀ α, w α ∈ P ↔ α ∈ Q) :
    (rootAction hD).range = reflectionGroup hD P := by
  have hsub : reflectionGroup hD P ≤ (rootAction hD).range := by
    rw [reflectionGroup, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hreflection i
  apply le_antisymm _ hsub
  rintro _ ⟨n, rfl⟩
  obtain ⟨w, hw, hwp⟩ := hchambers ((rootAction hD n⁻¹) ⁻¹' P)
    (rootAction_positive_preimage hD hadd hP n⁻¹)
  obtain ⟨m, hm⟩ := hsub hw
  have hmn : (m * n).val ∈ T.toSubgroup := by
    apply hstabilizer (m * n)
    intro α
    have h := hwp (rootAction hD n α)
    change w (rootAction hD n α) ∈ P ↔ rootAction hD n⁻¹ (rootAction hD n α) ∈ P at h
    have hinv : rootAction hD n⁻¹ (rootAction hD n α) = α := by
      rw [map_inv]
      exact Equiv.symm_apply_apply _ _
    rw [hinv] at h
    simpa only [map_mul, Equiv.Perm.mul_apply, hm] using h
  have hker : m * n ∈ (rootAction hD).ker := torus_le_kernel hD hT hmn
  change rootAction hD (m * n) = 1 at hker
  rw [map_mul, hm] at hker
  rw [eq_inv_of_mul_eq_one_right hker]
  exact (reflectionGroup hD P).inv_mem hw

/-- Assemble the literal normalizer action after the independent geometric and
root-system assertions have been proved. No SL₂ marking or selected lift is used. -/
public theorem nonempty_of_chamber_geometry (hT : IsSubtorus T)
    (hadd : D.IsRootAdditionComplete) (hP : IsPositiveSystem D P)
    (hmult : ∀ α, RootWeightSpaceMultiplicityOne T (D.rootWeight α))
    (hstabilizer : ∀ n : T.normalizer.toSubgroup,
      (∀ α, rootAction hD n α ∈ P ↔ α ∈ P) → n.val ∈ T.toSubgroup)
    (hreflection : ∀ i : {α // α ∈ FundamentalRootsFor D P},
      reflectionPerm hD i.val ∈ (rootAction hD).range)
    (hchambers : ∀ Q : Set D.Root, IsPositiveSystem D Q →
      ∃ w ∈ reflectionGroup hD P, ∀ α, w α ∈ P ↔ α ∈ Q)
    (hpositive : ∀ (i : {α // α ∈ FundamentalRootsFor D P}) β,
      β ∈ P → β ≠ i.val → D.reflect i.val β ∈ P) :
    Nonempty (NormalizerRootAction D P) := by
  exact ⟨{
    action := rootAction hD
    kernel := kernel_eq_of_chamber_stabilizer hD hT hstabilizer
    transport := rootAction_transport hD hmult
    neg := rootAction_neg hD
    reflection := fun i => reflectionPerm hD i.val
    reflection_apply := fun i β => reflectionPerm_apply hD i.val β
    range_eq := range_eq_of_chamber_reduction hD hT hadd hP hstabilizer hreflection hchambers
    other_positive := hpositive }⟩

include hD in
/-- In the empty-root case the Borel witness identifies `B = T`. Thus the
source self-normalizer theorem alone supplies the remaining geometric input;
all reflection and positivity assertions are vacuous. -/
public theorem nonempty_of_empty_roots_of_borel_self_normalizing
    [IsEmpty D.Root] (hT : IsSubtorus T)
    (hadd : D.IsRootAdditionComplete) (hP : IsPositiveSystem D P)
    {B : ClosedSubgroup G} (hBP : IsBorelOfPositiveSystem D P B)
    (hself : B.normalizer.toSubgroup = B.toSubgroup) :
    Nonempty (NormalizerRootAction D P) := by
  have hPempty : P = ∅ := by ext α; exact isEmptyElim α
  have hBT : B.toSubgroup = T.toSubgroup := by
    rw [hBP.torus_unipotent_generate, hBP.root_generated, hPempty,
      RootSubgroupGenerated_empty, sup_bot_eq]
  have hBTclosed : B = T := by
    apply SetLike.coe_injective
    ext x
    change x ∈ B.toSubgroup ↔ x ∈ T.toSubgroup
    rw [hBT]
  apply nonempty_of_chamber_geometry hD hT hadd hP
  · exact fun α => isEmptyElim α
  · intro n _
    have hn : n.val ∈ B.normalizer.toSubgroup := by
      simpa only [hBTclosed] using n.property
    rwa [hself, hBT] at hn
  · exact fun i => isEmptyElim i.val
  · intro Q _
    exact ⟨1, (reflectionGroup hD P).one_mem, fun α => isEmptyElim α⟩
  · exact fun i => isEmptyElim i.val

end Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.NormalizerActionExistence
