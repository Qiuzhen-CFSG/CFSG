module

public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.A6Lift.Model
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The flag for the actual component Sylow intersection

Restrict the prescribed ambient Sylow to the normal component image, then
carry that literal intersection through the marked Sp₄(2)′ isomorphism.
Its invariant line and plane have the computed orthogonal preimage and
irreducible model stabilizers. In particular the first preimage is the
two-dimensional Sylow-fixed space and has a unique singular complement
to its nonzero radical. No Sylow alignment is an additional premise.

Source: Aschbacher--Smith I.2.3(1a),(2), printed p.413, in the binary
covering case used before 14.6.24, printed p.1038.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.A6Lift
open Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Representation.SymplecticFourOrthogonalCover.SylowFlag
open Representation.BinaryOffender ClassicalOrthogonal Module
variable {J : Type*} [Group J] [Finite J]

/-- The literal intersection S ∩ L supplies the model flag and the unique
singular point above the line selected by the original ambient Sylow. -/
theorem selected_sylow_flag
    (L : Subgroup J) [L.Normal] (e : L ≃* Core)
    (η : Representation (ZMod 2) J Natural)
    (hη : ∀ l : L, ∀ v, η l v = natural e l v)
    (S : Sylow 2 J) (line : Submodule (ZMod 2) Natural)
    (hd : finrank (ZMod 2) line = 1)
    (hS : S.toSubgroup ≤ subspaceStabilizer η line) :
    ∃ R : Sylow 2 Core,
      (R : Subgroup Core) = ((S : Subgroup J).subgroupOf L).map e.toMonoidHom ∧
      ∃ plane : Submodule (ZMod 2) Natural,
        finrank (ZMod 2) plane = 2 ∧ line ≤ plane ∧
        (∀ v ∈ line, ∀ w ∈ line, (formD 2 (ZMod 2)).polarBilin v w = 0) ∧
        (∀ v ∈ plane, ∀ w ∈ plane, (formD 2 (ZMod 2)).polarBilin v w = 0) ∧
        IsIrreducible (stabilizerRepresentation (binaryNatural (K := ZMod 2))
          (line.restrictScalars (ZMod 2))) ∧
        IsIrreducible (stabilizerRepresentation (binaryNatural (K := ZMod 2))
          (plane.restrictScalars (ZMod 2))) ∧
        line.comap projection.toLinearMap =
          fixed ((action (K := ZMod 2)).comp R.toSubgroup.subtype) ∧
        finrank (ZMod 2) (line.comap projection.toLinearMap) = 2 ∧
        ∃! P : Submodule (ZMod 2) Cover,
          finrank (ZMod 2) P = 1 ∧ (∀ u ∈ P, formB 2 (ZMod 2) u = 0) ∧
          Disjoint P radical ∧ line.comap projection.toLinearMap = P ⊔ radical := by
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal L
  let R : Sylow 2 Core := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hR : (R : Subgroup Core) = ((S : Subgroup J).subgroupOf L).map e.toMonoidHom := by
    change (P : Subgroup L).map e.toMonoidHom = _
    rw [hP]
  have h1 : ∀ t : R.toSubgroup,
      line ≤ line.comap (symplecticDerivedNatural 2 t.val) := by
    intro t u hu
    have ht : t.val ∈ (P : Subgroup L).map e.toMonoidHom := t.property
    obtain ⟨l, hl, hel⟩ := ht
    have hls : (l : J) ∈ (S : Subgroup J) := by
      change l ∈ (S : Subgroup J).subgroupOf L
      rw [← hP]
      exact hl
    have hx := (hS hls u).mpr hu
    rw [hη] at hx
    change symplecticDerivedNatural 2 (e l) u ∈ line at hx
    change symplecticDerivedNatural 2 t.val u ∈ line
    rwa [show e l = t.val from hel] at hx
  obtain ⟨g, _, _, d2, _, h2, _, _⟩ := exists_unique_flag R
  obtain ⟨hle, hi1, hi2⟩ := ChapterI.ModuleCovers.SymplecticFour.selected_flag_isotropic
    R line (movedPlane g) h1 hd h2 d2
  obtain ⟨hirr1, hirr2⟩ :=
    ChapterI.ModuleCovers.SymplecticFour.selected_flag_stabilizers_irreducible
      R line (movedPlane g) h1 hd h2 d2
  obtain ⟨hpre, dpre, hsing⟩ := ChapterI.ModuleCovers.SymplecticFour.selected_first_preimage
    R line h1 hd
  exact ⟨R, hR, movedPlane g, d2, hle, hi1, hi2, hirr1, hirr2, hpre, dpre, hsing⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.A6Lift
