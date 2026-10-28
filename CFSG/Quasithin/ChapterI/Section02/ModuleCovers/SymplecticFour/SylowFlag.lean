module

public import CFSG.Quasithin.ChapterI.Section02.ModuleCovers.SymplecticFour
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag

/-!
# I.2.3: the selected Sylow flag of the genuine Sp₄′ cover

The defining source assumptions select an invariant line and plane of the
natural module. Derived-Sylow conjugacy and invariant-space uniqueness identify
them without a supplied alignment. The first literal preimage is the fixed
two-space and has a unique singular projective point complementing the radical.
The isotropy conclusions are the model inputs used by `OriginalAction`.

Source: Aschbacher–Smith, I.2.3(1a),(2), printed p.413 / PDF p.424.
The original ambient-action application still needs the stabilizer
irreducibility supplied separately from this geometric calculation.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterI.ModuleCovers.SymplecticFour
open Representation Representation.OneCohomology ClassicalOrthogonal
open Representation.SymplecticFourOrthogonalCover
open Representation.SymplecticFourOrthogonalCover.SylowFlag
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- I.2.3(1a) for the actual selected natural line and literal orthogonal projection. -/
theorem selected_first_preimage (S : Sylow 2 (L (K := F)))
    (V1 : Submodule F (Natural (K := F)))
    (h1 : ∀ t : (S : Subgroup (L (K := F))), V1 ≤ V1.comap (symplecticDerivedNatural 2 t.val))
    (d1 : Module.finrank F V1 = 1) :
    V1.comap projection.toLinearMap = fixed ((action (K := F)).comp (S : Subgroup (L (K := F))).subtype) ∧
      Module.finrank F (V1.comap projection.toLinearMap) = 2 ∧
      ∃! P : Submodule F (Space (K := F)),
        Module.finrank F P = 1 ∧ (∀ x ∈ P, formB 2 F x = 0) ∧
        Disjoint P radical ∧ V1.comap projection.toLinearMap = P ⊔ radical := by
  obtain ⟨g,hg⟩ := exists_marking S
  have e1 := movedLine_unique g V1 (hg ▸ h1) d1
  refine ⟨?_,?_,movedPoint g,?_,?_⟩
  · rw [hg,e1]
    exact (moved_cover_fixed g).symm
  · rw [e1]
    exact moved_preimage_finrank g
  · refine ⟨movedPoint_finrank g,movedPoint_singular g,movedPoint_disjoint g,?_⟩
    rw [e1]
    exact movedLine_preimage g
  · intro P hP
    apply moved_singular_unique g P _ hP.1 hP.2.1
    rw [← e1,hP.2.2.2]
    exact le_sup_left

/-- The actual selected line and plane are isotropic for the natural polar form,
as required by the original-action proof of I.2.3(2). -/
theorem selected_flag_isotropic (S : Sylow 2 (L (K := F)))
    (V1 V2 : Submodule F (Natural (K := F)))
    (h1 : ∀ t : (S : Subgroup (L (K := F))), V1 ≤ V1.comap (symplecticDerivedNatural 2 t.val))
    (d1 : Module.finrank F V1 = 1)
    (h2 : ∀ t : (S : Subgroup (L (K := F))), V2 ≤ V2.comap (symplecticDerivedNatural 2 t.val))
    (d2 : Module.finrank F V2 = 2) :
    V1 ≤ V2 ∧
      (∀ x ∈ V1, ∀ y ∈ V1, (formD 2 F).polarBilin x y = 0) ∧
      (∀ x ∈ V2, ∀ y ∈ V2, (formD 2 F).polarBilin x y = 0) := by
  obtain ⟨g,hg⟩ := exists_marking S
  have e1 := movedLine_unique g V1 (hg ▸ h1) d1
  have e2 := movedPlane_unique g V2 (hg ▸ h2) d2
  rw [e1,e2]
  exact ⟨movedLine_le_plane g, fun x hx y hy => movedLine_isotropic g x y hx hy,
    fun x hx y hy => movedPlane_isotropic g x y hx hy⟩

/-- The source line and its root intersection are transported by the same actual
derived-group element. In particular this supplies the nonbinary central-root
placement, without asserting that a binary full-group transvection is derived. -/
theorem selected_root_placement (S : Sylow 2 (L (K := F)))
    (V1 : Submodule F (Natural (K := F)))
    (h1 : ∀ t : (S : Subgroup (L (K := F))), V1 ≤ V1.comap (symplecticDerivedNatural 2 t.val))
    (d1 : Module.finrank F V1 = 1) :
    ∃ g : L (K := F), (S : Subgroup (L (K := F))) = movedSylow g ∧
      V1 = movedLine g ∧
      movedRoot g ≤ (Subgroup.center (S : Subgroup (L (K := F)))).map (S : Subgroup (L (K := F))).subtype := by
  obtain ⟨g,hg⟩ := exists_marking S
  refine ⟨g,hg,movedLine_unique g V1 (hg ▸ h1) d1,?_⟩
  rw [hg]
  exact movedRoot_central g

end CFSG.Quasithin.ChapterI.ModuleCovers.SymplecticFour
