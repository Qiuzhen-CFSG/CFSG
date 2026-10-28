module

public import Theory.Representation.SL2OrthogonalCover.Sylow
public import Mathlib.Algebra.Algebra.ZMod

/-!
# I.2.3: the orthogonal SL₂ branch

The universal binary L-cover is the explicit three-dimensional orthogonal
space constructed below, over the given natural projection. Its polar radical
is the one-dimensional fixed kernel. The Sylow statements give the unique
singular point, nonsingular pairwise-disjoint root displacement lines, and the
whole root commutator. For arbitrary binary covers, the inverse image of the
natural fixed F-line is the root commutator and is fixed by the root group.

This is the universal L-cover interpretation, for all |F|=2ⁿ with n>1,
including q=4. The original ambient G interpretation remains with the parent
I.2.3 assembly. `LinearTwo.CoverLift` supplies the Chapter E application.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.3(1a,b),(3),
printed p.413/PDF p.424, using I.1.5 and I.1.6, printed p.408.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterI.ModuleCovers.LinearTwo
open Representation Representation.OneCohomology Representation.SL2OrthogonalCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The nondegenerate orthogonal model, its fixed polar radical, and the
map-compatible identification with the actual universal binary covering space. -/
theorem universal_orthogonal (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    (form (F := F)).Nondegenerate ∧
      (∀ g v, (form (F := F)) ((action (F := F)) g v) = (form (F := F)) v) ∧
      fixed (action (F := F)) = (form (F := F)).polarBilin.ker ∧
      Module.finrank F (form (F := F)).polarBilin.ker = 1 ∧
      ∃ e : Module.Dual (ZMod 2) (cocycles (binaryNatural (F := F)).dual) ≃ₗ[ZMod 2] Space F,
        (∀ g u, e ((universalAction (binaryNatural (F := F)).dual).dual g u) = (action (F := F)) g (e u)) ∧
        ∀ u, (projection (F := F)) (e u) = universalCoverProjection (binaryNatural (F := F)) u :=
  ⟨form_nondegenerate, form_invariant, fixed_radical, radical_dimension, universal_equiv (F := F) n hn hF⟩

/-- All source root-geometry clauses (1a,b) hold at every Sylow of SL₂(F). -/
theorem sylow_root_geometry (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 (SL F)) :
    (∃ P : Submodule F (Space F), Module.finrank F P = 1 ∧
      fixed ((action (F := F)).comp S.toSubgroup.subtype) = P ⊔ (form (F := F)).polarBilin.ker ∧
      Disjoint P (form (F := F)).polarBilin.ker ∧
      ∀ v ∈ fixed ((action (F := F)).comp S.toSubgroup.subtype), (form (F := F)) v = 0 ↔ v ∈ P) ∧
    (∀ r ∈ S, r ≠ 1 → Module.finrank F (movedSpace r) = 1 ∧
      movedSpace r ≤ fixed ((action (F := F)).comp S.toSubgroup.subtype) ∧
      (∀ v ∈ movedSpace r, v ≠ 0 → (form (F := F)) v ≠ 0) ∧
      movedSpace r ≠ (form (F := F)).polarBilin.ker) ∧
    (∀ r ∈ S, ∀ s ∈ S, r ≠ 1 → s ≠ 1 → r ≠ s → Disjoint (movedSpace r) (movedSpace s)) ∧
    Coinvariants.ker ((action (F := F)).comp S.toSubgroup.subtype) =
      fixed ((action (F := F)).comp S.toSubgroup.subtype) :=
  ⟨sylow_fixed_geometry S,
    fun r hr hr1 => sylow_displacement_geometry S r hr hr1,
    fun r hr s hs hr1 hs1 hrs => sylow_displacements_disjoint S r s hr hs hr1 hs1 hrs,
    sylow_commutator (card_gt_two n hn hF) S⟩

/-- I.2.3(3), with an arbitrary binary covering space and arbitrary Sylow root.
The first subspace is the literal preimage of the natural fixed line. -/
theorem arbitrary_cover (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (SL F) W}
    (p : σ.IntertwiningMap (binaryNatural (F := F))) (hp : IsCover p) (S : Sylow 2 (SL F)) :
    let V₁ := (fixed ((binaryNatural (F := F)).comp S.toSubgroup.subtype)).comap p.toLinearMap
    fixed σ ≤ V₁ ∧ V₁ = Coinvariants.ker (σ.comp S.toSubgroup.subtype) ∧
      V₁ ≤ fixed (σ.comp S.toSubgroup.subtype) :=
  cover_sylow_geometry n hn hF p hp S

end CFSG.Quasithin.ChapterI.ModuleCovers.LinearTwo
