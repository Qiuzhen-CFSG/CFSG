module

public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.LocalCover
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.DefectVanishing
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.FieldInvariants

/-!
# Splitting ordinary Suzuki covering groups

For a finite perfect central covering of the literal Suzuki matrix group,
`Family.rootData` constructs its lifted root subgroup, marked additive-field
abelianization, central two-group stem kernel and scalar split-torus action.
All third commutators lie in that kernel, and the torus fixes it pointwise.
`Family.canonicalRootData` applies this to the canonical universal covering;
`Family.canonicalKernel_eq_bot_of_local` transfers local kernel triviality
to the full Schur kernel.

For `m ≥ 2`, the defining binary field has dimension at least five. The
finite-field calculation kills all scalar-invariant pairings and triple maps.
Applying central-defect vanishing to the canonical local data therefore proves
`Family.canonicalKernel_eq_bot`, with no additional premises. Inverting the
now-bijective universal projection gives `Family.rootSection`, whose composite
with that literal projection is the standard root-subgroup inclusion.

The exceptional parameter `m = 1` also satisfies the local group data, but its
field has dimension three, so the triple-map vanishing argument does not apply.

Source: the exhaustive multiplier list in Aschbacher--Smith I.1.3, printed
p.407/PDF p.418 of `refs/quasithin.pdf`; GLS3 §6.1. The marked root and torus
formulas are Huppert--Blackburn III, XI.3.1.
-/

public noncomputable section

namespace BenderSuzuki.MatrixGroups.SchurCover.Family
open Theory.GroupTheory

/-- The ordinary Suzuki groups `Sz(2^(2*m+1))`, starting at `Sz(32)`, have
trivial canonical Schur kernel. Both finite-field inputs are discharged. -/
theorem canonicalKernel_eq_bot (m : ℕ) (hm : 2 ≤ m) : Kernel m = ⊥ := by
  let : Fact (0 < m) := ⟨by omega⟩
  exact canonicalKernel_eq_bot_of_invariants m (pairingsVanish m hm) (triplesVanish m hm)

private def projectionEquiv (m : ℕ) (hm : 2 ≤ m) :
    CoverGroup m ≃* SuzukiMatrixGroup m := by
  letI : Fact (0 < m) := ⟨by omega⟩
  exact MulEquiv.ofBijective
    (PerfectCentralCovering.universalProjection (SuzukiMatrixGroup m))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (canonicalKernel_eq_bot m hm),
      PerfectCentralCovering.universalProjection_surjective _⟩

/-- A homomorphic section of the universal projection over the literal
standard Suzuki root subgroup, for every ordinary parameter. -/
def rootSection (m : ℕ) (hm : 2 ≤ m) :
    SuzukiRootSubgroup m →* CoverGroup m :=
  (projectionEquiv m hm).symm.toMonoidHom.comp (SuzukiRootSubgroup m).subtype

/-- The constructed section projects to the original root-subgroup inclusion. -/
theorem universalProjection_comp_rootSection (m : ℕ) (hm : 2 ≤ m) :
    (PerfectCentralCovering.universalProjection (SuzukiMatrixGroup m)).comp
      (rootSection m hm) = (SuzukiRootSubgroup m).subtype := by
  apply MonoidHom.ext
  intro x
  exact (projectionEquiv m hm).apply_symm_apply x

end BenderSuzuki.MatrixGroups.SchurCover.Family

end
