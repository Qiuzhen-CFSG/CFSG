module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientCalculations
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylWords

/-!
# Relative root factors for concrete Ree word exchange

The two positive simple relative root groups are the actual fixed
intersections of the complete end-node and middle-node root subsystems.
In particular, the middle block includes all four positive B₂ roots.

The three explicit calculations below separate the proof of exchange into
Borel collection, a rank-one Gauss equation retaining its fixed torus factor,
and the sign of a complete relative block under a normalizer word. They are
proof obligations, not assumed properties of the model. `Reduction` proves
that their conjunction gives the concrete exchange formula; final assembly
must establish them.

Source: GLS3 2.3.4–8 and §2.4, Table 2.4, types V and VI,
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.SectionGeometry.BNPair
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open LargeLocalSeeds Parabolics Parabolics.Binary.FixedGeometry
open LocalBlockInput.PairRigidity LocalBlockInput.PairRigidity.FixedCollection

/-- The full fixed positive root group on a simple relative root. -/
def relativePositiveBlock (m : ℕ) (s : Side) : Subgroup (Model m) :=
  (splitSimpleBlock m s true).comap (toSplitGroup m)

theorem relativePositiveBlock_le_unipotent (m : ℕ) (s : Side) :
    relativePositiveBlock m s ≤ unipotent m := by
  apply comap_mono
  apply Subgroup.closure_mono
  rintro x ⟨r, t, hr, rfl⟩
  exact ⟨r, t, hr.2, rfl⟩

theorem relativePositiveBlock_le_borel (m : ℕ) (s : Side) :
    relativePositiveBlock m s ≤ borel m :=
  (relativePositiveBlock_le_unipotent m s).trans (unipotent_le_borel m)

/-- The comparison with a supplied local twist preserves the actual matrices. -/
theorem modelEquiv_mem_relativePositiveBlock_iff {m : ℕ} (d : LocalBlockInput m)
    (s : Side) (x : d.fixedGroup) :
    d.modelEquiv x ∈ relativePositiveBlock m s ↔ x ∈ simpleBlock d s true := by
  change toSplitGroup m (d.modelEquiv x) ∈ splitSimpleBlock m s true ↔
    x.val ∈ splitSimpleBlock m s true
  simp only [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]

theorem wordExchange_modelEquiv_relativeWeyl {m : ℕ} (d : LocalBlockInput m) (s : Side) :
    d.modelEquiv (relativeWeyl d s) = weylLift m s := by
  apply toSplitGroup_injective m
  simp only [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe, relativeWeyl_val]
  rfl

/-- Collect the full Borel with the distinguished positive block last.
The complementary factor stays in the Borel under the relative reflection. -/
def BorelSimpleFactorization (m : ℕ) : Prop :=
  ∀ s : Side, ∀ b ∈ borel m,
    ∃ b₀ ∈ borel m, ∃ x ∈ relativePositiveBlock m s,
      b = b₀ * x ∧ weylLift m s * b₀ * weylLift m s ∈ borel m

/-- The nonzero rank-one Gauss equation, with its full fixed torus factor. -/
def RelativeRankOneGauss (m : ℕ) : Prop :=
  ∀ s : Side, ∀ x ∈ relativePositiveBlock m s, x ≠ 1 →
    ∃ a ∈ relativePositiveBlock m s, ∃ t ∈ fixedTorus m,
      ∃ y ∈ relativePositiveBlock m s,
        weylLift m s * x * weylLift m s = a * t * weylLift m s * y

/-- One of the two complete signed simple blocks has positive conjugate.
The two alternatives concern all elements of the chosen block together. -/
def RelativeBlockSign (m : ℕ) : Prop :=
  ∀ s : Side, ∀ n ∈ normalizerWords m,
    (∀ x ∈ relativePositiveBlock m s, n⁻¹ * x * n ∈ borel m) ∨
      (∀ x ∈ relativePositiveBlock m s,
        n⁻¹ * (weylLift m s * x * weylLift m s) * n ∈ borel m)

end ReeF4.SectionGeometry.BNPair
