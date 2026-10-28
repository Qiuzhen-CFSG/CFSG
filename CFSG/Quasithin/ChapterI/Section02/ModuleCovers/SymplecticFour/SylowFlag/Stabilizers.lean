module

public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag.Stabilizers
public import CFSG.Quasithin.ChapterI.Section02.ModuleCovers.SymplecticFour

/-!
# I.2.3: binary irreducibility of the selected Sp₄′ flag stabilizers

The actual Sylow invariance and dimensions identify the selected natural line
and plane with a conjugate of the standard flag. The literal stabilizers in the
derived matrix group are irreducible after restriction to F₂, including F = F₂.
This supplies the model stabilizer input for the original-action theorem
`ModuleCovers.OriginalAction.fixed_point_and_normalizer_centrality`.

Source: Aschbacher–Smith, I.2.3(2) and its proof, printed p.413 / PDF p.424.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterI.ModuleCovers.SymplecticFour
open Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Representation.SymplecticFourOrthogonalCover.SylowFlag
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Both selected natural subspaces have binary-irreducible literal stabilizers;
no alignment or irreducibility hypothesis is required. -/
theorem selected_flag_stabilizers_irreducible (S : Sylow 2 (L (K := F)))
    (V1 V2 : Submodule F (Natural (K := F)))
    (h1 : ∀ t : (S : Subgroup (L (K := F))),
      V1 ≤ V1.comap (symplecticDerivedNatural 2 t.val))
    (d1 : Module.finrank F V1 = 1)
    (h2 : ∀ t : (S : Subgroup (L (K := F))),
      V2 ≤ V2.comap (symplecticDerivedNatural 2 t.val))
    (d2 : Module.finrank F V2 = 2) :
    IsIrreducible (BinaryOffender.stabilizerRepresentation (binaryNatural (K := F))
      (V1.restrictScalars (ZMod 2))) ∧
    IsIrreducible (BinaryOffender.stabilizerRepresentation (binaryNatural (K := F))
      (V2.restrictScalars (ZMod 2))) := by
  obtain ⟨g,hg⟩ := exists_marking S
  have e1 := movedLine_unique g V1 (hg ▸ h1) d1
  have e2 := movedPlane_unique g V2 (hg ▸ h2) d2
  rw [e1,e2]
  exact ⟨movedLine_stabilizer_irreducible g, movedPlane_stabilizer_irreducible g⟩

end CFSG.Quasithin.ChapterI.ModuleCovers.SymplecticFour
