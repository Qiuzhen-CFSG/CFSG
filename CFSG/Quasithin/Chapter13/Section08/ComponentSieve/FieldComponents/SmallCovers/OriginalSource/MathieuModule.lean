module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.Mathieu
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Exclusion
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.NativeSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource.Seed

/-!
# Applying the Mathieu module obstruction to the original source

The original flag has |V₃:V₁| = 4. The actual point residual moves V₃,
normalizes it, and is transitive on the nonzero vectors of V₃/V₁. Hence the
literal seed is irreducible under L₁T. With the constructed Mathieu
placement, these facts discharge all group-seed premises of the existing
central-code obstruction on I/C_I(K*). No splitting of I is used.

The native source classification and strict cocode estimate discharge the
B.4 representation contracts in the final application. Only the complete
relevant F.9.18 outputs remain explicit there. Their original source
construction and the remaining field/cover branches belong to
qt-d-138-fields-source; qt-d-1381-source supplies the SourceContext.
These applications do not assert the unconditional ordinary-local Mathieu
exclusion.
Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973),
using 13.7.3(6), F.9.18(2–4),(7), B.4.2 and B.4.5.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
open SourceCompletion LinearThree.Geometry.CoveredProduct.ResidualPlacement
open AlternatingAndLinear.FourStructure.OriginalSource
open Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The actual central-code witness contradicts the original seed. All
placement, seed, fixed-line and quotient-embedding premises are discharged;
the invariant moved space and its code recognition remain explicit. -/
theorem source_mathieu_central_code_false
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22)
    (act : Mathieu.SourceAction H V₃ V₁)
    (I : Subrepresentation act.representation)
    (hI : I.toSubmodule = subspaceCommutator act.representation ⊤ (Source.starImage H K))
    (hcode : MathieuCode.IsM22Code
      ((Mathieu.sourceCentralRepresentation H K (one L T V₁) (T : Subgroup G) G₁ M V₃ V₁
        (sourceMathieuSetup c eK) act I).comp (Source.starImage H K).subtype)) : False := by
  have hH := c.component.local_overgroup
  exact Mathieu.source_central_code_contradiction_of_group_seed H K (one L T V₁)
    (T : Subgroup G) G₁ M V₃ V₁ (sourceMathieuSetup c eK) act
    (c.f9 H hH).point_lt (seed_index_source c.localSetup)
    (Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup c.localSetup))
    (sup_le (Section07.ModelExclusions.point_residual_normalizes_seed
      (localNaturalSetup c.localSetup)) c.localSetup.seed_stable)
    (fun X hx hy hn => seed_irreducible_source c.localSetup (le_sup_left.trans hH.1.2)
      act.representation act.conjugation X hx hy (le_sup_left.trans hn))
    I hI hcode MathieuCode.m24OctadFixedLine

/-- Original-source application of the complete earlier representation
contracts. No Mathieu placement or group-seed callback remains. The
field-sieve owner retains construction of the displayed earlier inputs. -/
theorem source_mathieu_false_of_earlier
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22)
    (act : Mathieu.SourceAction H V₃ V₁)
    (hB42 : Mathieu.Recognition.SourceB4.FullB42.{u,u} KnownSimple.IsKnownSimple)
    (hB45 : FullB45.{u,u} KnownSimple.IsKnownSimple)
    (hF918 : Mathieu.Recognition.F918Source.Earlier (sourceMathieuSetup c eK) act L) : False := by
  obtain ⟨w⟩ := Mathieu.Recognition.F918Source.centralWitness_of_earlier
    (sourceMathieuSetup c eK) act c.component.sqtk
    (Mathieu.Recognition.SourceB4.noFaithfulFF hB42)
    (Mathieu.Recognition.SourceB4.smallQuadraticCode hB42 hB45) hF918
  exact source_mathieu_central_code_false c eK act w.I w.moved w.code

/-- The original Mathieu contradiction with both B.4 premises discharged.
Only the genuine earlier F.9.18 data remain with this field-sieve owner. -/
theorem source_mathieu_false_of_f918
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22)
    (act : Mathieu.SourceAction H V₃ V₁)
    (hF918 : Mathieu.Recognition.F918Source.Earlier (sourceMathieuSetup c eK) act L) : False := by
  obtain ⟨w⟩ := Mathieu.Recognition.F918Source.centralWitness_of_earlier
    (sourceMathieuSetup c eK) act c.component.sqtk
    Mathieu.Recognition.NativeSource.noFaithfulFF
    Mathieu.Recognition.NativeSource.smallQuadraticCode hF918
  exact source_mathieu_central_code_false c eK act w.I w.moved w.code

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
