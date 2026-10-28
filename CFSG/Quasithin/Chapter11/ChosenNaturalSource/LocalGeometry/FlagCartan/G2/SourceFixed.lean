module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.SourceFlag

/-!
# The original inner Sylow cannot centralize the second flag space

Conjugation through the unchanged marking sends every inner-Sylow fixed
vector into the first model line. Surjectivity of the original projection
then excludes centralization of the second preimage by that Sylow. This
retains arbitrary central kernel in V and isolates the fixed-space issue
in the local argument of Aschbacher--Smith 11.1.4, printed p.765.
-/

@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

/-- Actual fixed elements of V under T intersect L lie in the first preimage. -/
theorem inner_fixed_le_first :
    V ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ≤ (flag S m).Vi 0 := by
  rintro v ⟨hv,hfix⟩
  apply ((coordinates S m).mem_preimage _ ⟨v,hv⟩).mpr
  apply ((modelFlag S m).first _).mpr
  rintro ⟨q,hq⟩
  change q ∈ (innerSylow (D := D) : Subgroup L).map (derivedMap S m) at hq
  obtain ⟨l,hl,rfl⟩ := hq
  rw [innerSylow_coe] at hl
  have he : V.normalizerMonoidHom (inclusion D.normalizes l) ⟨v,hv⟩ = ⟨v,hv⟩ := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hfix l.val ⟨hl,l.property⟩)
  have hh := (coordinates S m).projection_component_conjugation l ⟨v,hv⟩
  rw [he] at hh
  exact hh.symm

/-- The genuine second preimage is not centralized by the original inner Sylow. -/
theorem plane_not_le_inner_centralizer :
    ¬ (flag S m).Vi 1 ≤ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  intro hc
  have h : (flag S m).Vi 1 ≤ (flag S m).Vi 0 :=
    (le_inf (D.centralQuotientPreimage_le _) hc).trans (inner_fixed_le_first S m)
  have hfield : (modelFlag S m).space 1 ≤ (modelFlag S m).space 0 :=
    (coordinates S m).preimage_le_iff _ _ |>.mp h
  have hd := Submodule.finrank_mono hfield
  rw [(modelFlag S m).dimension 1, (modelFlag S m).dimension 0] at hd
  norm_num at hd

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2
