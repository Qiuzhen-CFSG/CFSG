module

public import CFSG.Quasithin.ChapterI.Section02.ModuleCovers.SymplecticFour
public import Theory.Representation.SymplecticFourOrthogonalCover.Roots.Conjugates
public import Theory.Representation.SymplecticFourOrthogonalCover.Roots.Binary

/-!
# I.2.3: root geometry in the five-dimensional orthogonal cover

The literal matrix roots in Sp₄(F)′ give nonsingular displacement points,
pairwise disjoint for distinct nonzero parameters. Their full commutator
is the first natural line's preimage and is root-fixed, also after actual
L-conjugation and passage to an arbitrary binary cover. All model premises
are discharged by the direct root calculation and the universal quotient.

Over F₂ the transvection is outside the genuine derived group and its root
intersection is trivial. The previously proved binary universal orthogonal
realization and fixed-space statements remain valid.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.3(1b),(3),
printed p.413/PDF p.424. The ambient G-action and Sylow flag identification
remain with the parent assembly and are not premises of these computations.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterI.ModuleCovers.SymplecticFour
open Representation Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Representation.SymplecticFourOrthogonalCover.Roots ClassicalOrthogonal
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- I.2.3(1b) on the actual derived root subgroup: each nonidentity root
has a nonsingular displacement point in the first preimage, distinct from
its polar radical. -/
theorem root_point_geometry (hcard : 2 < Nat.card F)
    (r : L (K := F)) (hr : r ∈ Roots.group) (hr1 : r ≠ 1) :
    let D := LinearMap.range (action r - LinearMap.id)
    Module.finrank F D = 1 ∧ D ≤ firstLine.comap projection.toLinearMap ∧
      (∀ v ∈ D, v ≠ 0 → formB 2 F v ≠ 0) ∧ D ≠ (formB 2 F).polarBilin.ker := by
  obtain ⟨t, rfl⟩ := (Roots.mem_group hcard r).mp hr
  have ht : t ≠ 0 := by
    intro ht
    apply hr1
    apply Subtype.ext
    change Representation.OneCohomology.SymplecticFour.rootElement 0 t = 1
    rw [ht, Theory.SpecificGroups.SymplecticFour.RootSubgroup.element_zero]
  refine ⟨rootDisplacement_dimension hcard t ht,
    rootDisplacement_le_firstPreimage hcard t,
    rootDisplacement_nonsingular hcard t ht, ?_⟩
  rw [← radical_eq_polar_ker]
  exact rootDisplacement_ne_radical hcard t ht

/-- I.2.3(1b), retaining the literal conjugated matrices and natural line. -/
theorem conjugate_root_points (hcard : 2 < Nat.card F) (g : L (K := F))
    (s t : F) (hs : s ≠ 0) (ht : t ≠ 0) (hst : s ≠ t) :
    let D := LinearMap.range (action (g * element hcard t * g⁻¹) - LinearMap.id)
    Module.finrank F D = 1 ∧ D ≤ (conjugateLine g).comap projection.toLinearMap ∧
      (∀ v ∈ D, v ≠ 0 → formB 2 F v ≠ 0) ∧ D ≠ radical ∧
      Disjoint (LinearMap.range (action (g * element hcard s * g⁻¹) - LinearMap.id)) D := by
  obtain ⟨hd, hp, hn, hr⟩ := conjugate_displacement_geometry hcard g t ht
  exact ⟨hd, hp, hn, hr, conjugate_displacements_disjoint hcard g s t hs hst⟩

/-- I.2.3(3) for every finite-dimensional binary cover, with its original
projection. The kernel is not assumed to be an F-module. -/
theorem arbitrary_cover_root_geometry (hcard : 2 < Nat.card F)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p) :
    fixed σ ≤ (firstLine.restrictScalars (ZMod 2)).comap p.toLinearMap ∧
      (firstLine.restrictScalars (ZMod 2)).comap p.toLinearMap =
        Coinvariants.ker (σ.comp Roots.group.subtype) ∧
      (firstLine.restrictScalars (ZMod 2)).comap p.toLinearMap ≤
        fixed (σ.comp Roots.group.subtype) :=
  cover_root_geometry hcard p hp

/-- The same source conclusion for each L-conjugate, on the original target. -/
theorem arbitrary_cover_conjugate_roots (hcard : 2 < Nat.card F) (g : L (K := F))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p) :
    fixed σ ≤ ((conjugateLine g).restrictScalars (ZMod 2)).comap p.toLinearMap ∧
      ((conjugateLine g).restrictScalars (ZMod 2)).comap p.toLinearMap =
        Coinvariants.ker (σ.comp (conjugateGroup g).subtype) ∧
      ((conjugateLine g).restrictScalars (ZMod 2)).comap p.toLinearMap ≤
        fixed (σ.comp (conjugateGroup g).subtype) :=
  cover_conjugate_root_geometry hcard g p hp

/-- The binary convention: the transvection root has trivial intersection
with the genuine derived group. All orthogonal-cover results still apply. -/
theorem binary_root_obstruction (hcard : Nat.card F = 2) :
    Roots.group (K := F) = ⊥ ∧
      ∀ g : Matrix.symplecticGroup (Fin 2) F,
        g * Representation.OneCohomology.SymplecticFour.rootElement 0 1 * g⁻¹ ∉
          commutator (Matrix.symplecticGroup (Fin 2) F) :=
  ⟨card_two_root_group_bot hcard, card_two_conjugate_root_not_mem_derived hcard⟩

end CFSG.Quasithin.ChapterI.ModuleCovers.SymplecticFour
