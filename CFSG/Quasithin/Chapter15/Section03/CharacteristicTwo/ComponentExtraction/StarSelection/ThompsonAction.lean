module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.Candidates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.MaximalImages
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives

/-!
# Classify the actual Thompson image

The actor is J(I)* inside I/C_I(U_I), with its literal conjugation action
on U_I. Maximum elementary subgroup images are best offenders. Their
generation proves B.5.3 internally in J(I)*; only containment in the full
ambient offender subgroup is asserted. Normality and two-reducedness
descend from I*, and the intrinsic J(I) supplies the actual SQTK cover.

The complete B.5.1/B.5.6 implications remain universal inputs for the
chosen class K. Applying them gives all source alternatives and trivial
three-prime core of J(I)*. Selecting a quotient component and lifting it
are separate remaining obligations; no component candidate is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.5–7,
printed p.76, B.5.3/6, pp.104–105, and 15.3.15/26, pp.1125 and 1130.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {G : Type u} [Group G]
namespace LocalData
variable (d : LocalData G)

/-- The literal image of the Thompson subgroup, not the whole star quotient. -/
noncomputable abbrev thompsonStar (I : Subgroup G) : Subgroup (d.Star I) :=
  d.starImage I (Stellmacher.elementaryAbelianMaxJ I)

/-- Restrict the genuine internal-module representation to the Thompson image. -/
noncomputable def thompsonStarAction (I : Subgroup G) (hZI : d.Z ≤ I)
    [IsElementaryAbelian 2 ((d.UI I).subgroupOf I)] :
    Representation (ZMod 2) (d.thompsonStar I) (Additive ((d.UI I).subgroupOf I)) :=
  (d.UIAction I hZI).comp (d.thompsonStar I).subtype

instance thompsonStar_normal (I : Subgroup G) : (d.thompsonStar I).Normal := by
  let _ := thompson_subgroupOf_normal I
  exact (inferInstance : ((Stellmacher.elementaryAbelianMaxJ I).subgroupOf I).Normal).map
    (d.starMap I) (QuotientGroup.mk'_surjective _)

/-- The restricted representation remains faithful. -/
theorem thompsonStarAction_faithful (I : Subgroup G) (hZI : d.Z ≤ I)
    [IsElementaryAbelian 2 ((d.UI I).subgroupOf I)] :
    Function.Injective (d.thompsonStarAction I hZI) :=
  (d.UIAction_faithful I hZI).comp (d.thompsonStar I).subtype_injective

variable [Finite G]

/-- Normality transfers two-reducedness to the actual Thompson image. -/
theorem thompsonStar_twoCore_eq_bot {I : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S) :
    pCore 2 (d.thompsonStar I) = ⊥ := by
  have hn : ((pCore 2 (d.thompsonStar I)).map (d.thompsonStar I).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hl : (pCore 2 (d.thompsonStar I)).map (d.thompsonStar I).subtype ≤
      pCore 2 (d.Star I) := le_sSup ⟨hn, pCore_isPGroup.map _⟩
  rw [d.star_twoCore_eq_bot hS hZS] at hl
  exact (map_eq_bot_iff_of_injective _ (d.thompsonStar I).subtype_injective).mp
    (le_bot_iff.mp hl)

/-- B.5.3 generation holds internally in J(I)*. This uses maximum
subgroup images, without identifying J(I)* with J(I*, U_I). -/
theorem thompsonStarAction_generated (I : Subgroup G) (hZI : d.Z ≤ I)
    [IsElementaryAbelian 2 ((d.UI I).subgroupOf I)] :
    offenderSubgroup (d.thompsonStarAction I hZI) = ⊤ := by
  apply map_injective (d.thompsonStar I).subtype_injective
  apply le_antisymm (by simp)
  rw [← MonoidHom.range_eq_map, range_subtype]
  change ((Stellmacher.elementaryAbelianMaxJ I).subgroupOf I).map (d.starMap I) ≤ _
  rw [thompson_subgroupOf]
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  apply map_le_iff_le_comap.mp
  by_cases hz : A.map (d.starMap I) = ⊥
  · rw [hz]; exact bot_le
  have ha := StarSelection.maxElementary_isBestOffender
    ((d.UI I).subgroupOf I) (d.starMap I) (QuotientGroup.mk'_surjective _)
    (d.starMap_ker hZI) ⊤ A le_top hA hz
  have hAN : A.map (d.starMap I) ≤ d.thompsonStar I := by
    change A.map (d.starMap I) ≤
      ((Stellmacher.elementaryAbelianMaxJ I).subgroupOf I).map (d.starMap I)
    rw [thompson_subgroupOf]
    exact map_mono (le_sSup hA)
  rw [← map_subgroupOf_eq_of_le hAN]
  apply map_mono
  exact le_iSup_of_le ((A.map (d.starMap I)).subgroupOf (d.thompsonStar I))
    (le_iSup_of_le ⟨ha.subgroupOf _ hAN, le_top⟩ le_rfl)

/-- The full ambient offender subgroup contains the Thompson image;
no equality with it is asserted. -/
theorem thompsonStar_le_offenderSubgroup (I : Subgroup G) (hZI : d.Z ≤ I)
    [IsElementaryAbelian 2 ((d.UI I).subgroupOf I)] :
    d.thompsonStar I ≤ offenderSubgroup (d.UIAction I hZI) := by
  change ((Stellmacher.elementaryAbelianMaxJ I).subgroupOf I).map (d.starMap I) ≤ _
  rw [thompson_subgroupOf]
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  apply map_le_iff_le_comap.mp
  by_cases hz : A.map (d.starMap I) = ⊥
  · rw [hz]; exact bot_le
  have ha := StarSelection.maxElementary_isBestOffender
    ((d.UI I).subgroupOf I) (d.starMap I) (QuotientGroup.mk'_surjective _)
    (d.starMap_ker hZI) ⊤ A le_top hA hz
  exact le_iSup_of_le _ (le_iSup_of_le ⟨ha, le_top⟩ le_rfl)

/-- The escaping Thompson image gives a nontrivial FF witness on the restricted action. -/
theorem thompsonStarAction_isFFModule (I : Subgroup G) (hZI : d.Z ≤ I)
    [IsElementaryAbelian 2 ((d.UI I).subgroupOf I)]
    (hJ : ¬ d.thompsonStar I ≤ d.starImage I d.M) :
    IsFFModule (d.thompsonStarAction I hZI) := by
  have hn : d.thompsonStar I ≠ ⊥ := fun h => hJ (h ▸ bot_le)
  let _ : Nontrivial (d.thompsonStar I) := (nontrivial_iff_ne_bot _).mpr hn
  by_contra hf
  have hb : offenderSubgroup (d.thompsonStarAction I hZI) ≤ ⊥ := by
    apply iSup_le
    intro A
    apply iSup_le
    intro hA
    exact (hf ⟨A, hA.1.isOffender _⟩).elim
  rw [d.thompsonStarAction_generated I hZI] at hb
  exact top_ne_bot (le_bot_iff.mp hb)

/-- B.5.3's cover is the intrinsic Thompson subgroup of I, with the
actual restricted star map as quotient projection. -/
noncomputable def thompsonStarSQTKQuotient {I : Subgroup G} {K : GroupClass.{u}}
    (hI : IsSQTK K I) : SQTKQuotient K (d.thompsonStar I) where
  Cover := (Stellmacher.elementaryAbelianMaxJ I).subgroupOf I
  kernel := ((d.starMap I).subgroupMap ((Stellmacher.elementaryAbelianMaxJ I).subgroupOf I)).ker
  sqtk := hI.subgroup _
  equiv := QuotientGroup.quotientKerEquivOfSurjective _
    ((d.starMap I).subgroupMap_surjective _)

/-- Every hypothesis of B.5.3, for precisely the actor classified in
15.3.15 and 15.3.26. -/
theorem thompsonStarFFHypothesis {I : Subgroup G} {K : GroupClass.{u}}
    (hI : IsSQTK K I) (hZI : d.Z ≤ I)
    [IsElementaryAbelian 2 ((d.UI I).subgroupOf I)]
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S) :
    FFHypothesis K (d.thompsonStarAction I hZI) where
  finite_module := Module.Finite.of_finite
  faithful := d.thompsonStarAction_faithful I hZI
  twoCore := d.thompsonStar_twoCore_eq_bot hS hZS
  generated := d.thompsonStarAction_generated I hZI
  quotient := ⟨d.thompsonStarSQTKQuotient hI⟩

/-- Apply the complete source interface, retaining the original action
and all B.5.1/B.5.6 module clauses. The universal theorem remains explicit. -/
theorem thompsonStar_sourceAlternative {I : Subgroup G} {K : GroupClass.{u}}
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} K)
    (hI : IsSQTK K I) (hZI : d.Z ≤ I)
    [IsElementaryAbelian 2 ((d.UI I).subgroupOf I)]
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S) :
    FFAlternatives.SourceAlternative (d.thompsonStarAction I hZI) :=
  classification.general _ _ _ (d.thompsonStarFFHypothesis hI hZI hS hZS)

/-- The actual Thompson image has trivial three-prime core, conditional
only on the complete classification and the earlier local inputs. -/
theorem thompsonStar_threePrimeCore_eq_bot {I : Subgroup G} {K : GroupClass.{u}}
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} K)
    (hI : IsSQTK K I) (hZI : d.Z ≤ I)
    [IsElementaryAbelian 2 ((d.UI I).subgroupOf I)]
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S)
    (hJ : ¬ d.thompsonStar I ≤ d.starImage I d.M) :
    pPrimeCore 3 (d.thompsonStar I) = ⊥ :=
  classification.threePrimeCore_eq_bot _ (d.thompsonStarFFHypothesis hI hZI hS hZS)
    (d.thompsonStarAction_isFFModule I hZI hJ)

end LocalData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
