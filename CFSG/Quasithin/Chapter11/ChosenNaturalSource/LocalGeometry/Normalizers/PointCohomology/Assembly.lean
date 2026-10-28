module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.Quotient.SourceReduction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core.RootPlacement

/-!
# Corrected point-cohomology calculation at the source consumer

First split at Q=VC_T(L). In the strict branch the actual block and marking
force Sp₄(4), and the constructed literal dual-model embedding gives the
point-fixed bound. Coprime Cartan decomposition then yields the omega-center
identity. Only the original point-core product and its fixed-space geometry
remain explicit here; their proofs belong to this same consolidated owner.
The normalizer-source parent supplies the block and later fixed-center inputs.

Source: Aschbacher–Smith 11.1.5, pp.765–766, with the C.1.13 denominator correction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The nonzero literal quotient forces q=4 and has the required original point-fixed bound. -/
theorem strict_quotient_point_fixed {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L)
    (hstrict : Nontrivial (((L ⊔ (T : Subgroup G)).pCoreIn 2) ⧸
      ((cohomologyDenominator T L V).subgroupOf ((L ⊔ (T : Subgroup G)).pCoreIn 2)))) :
    Nat.card S.field.Carrier = 4 ∧
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (f.Ri 0 : Set G) ≤
        cohomologyDenominator T L V := by
  refine ⟨(strict_quotient_symplectic_four D S c hb hstrict).1,?_⟩
  have hs : ChapterC.IsShort L := hb.elim (fun h => h.2.1) (fun h => h.1)
  cases c with
  | sl3 m => exact inf_le_left.trans (sl3_core_eq_denominator D S m hs).le
  | sp4 m => exact PointGeometry.Sp4Core.core_fixed_le_denominator D S m hs f
  | g2 m => exact (PointGeometry.no_g2_block_marking D S m hb).elim

/-- The entire cohomology step is discharged, with only local point-core geometry explicit. -/
theorem center_eq_of_core_calculations {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L)
    (hprod : f.Ri 0 = (f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hlocal : V ⊓ centralizer ((f.Li 0).pCoreIn 2 : Set G) = f.Vi 0) :
    radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L := by
  obtain ⟨X,hXL,hXR,hodd,hfixed,hpoint⟩ :=
    PointGeometry.center_geometry_of_core_calculations D S f hb hprod hlocal
  exact center_eq_of_strict_quotient_calculation D S hb f X hXL hXR hodd hfixed hpoint
    (fun hs => (strict_quotient_point_fixed D S f hb hs).2)

/-- Application to the parent normalizer theorem. The consolidated point-cohomology
owner retains the two local-core calculations; the normalizer-source parent owns
the permitted earlier block and later fixed-center premises. -/
theorem radicalAlternative_of_core_calculations {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hblocks : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
        (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L))
    (hcores : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      f.Ri 0 = (f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
        V ⊓ centralizer ((f.Li 0).pCoreIn 2 : Set G) = f.Vi 0)
    (hfixed : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
      normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G)) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree := by
  apply chosen_radicalAlternative_of_source_steps D S f hblocks _ hfixed
  intro he hb
  exact center_eq_of_core_calculations D S f hb (hcores he hb).1 (hcores he hb).2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
