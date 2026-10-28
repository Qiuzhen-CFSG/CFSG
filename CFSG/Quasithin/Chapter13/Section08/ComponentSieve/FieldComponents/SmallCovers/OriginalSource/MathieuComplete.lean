module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.MathieuModule
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.WholeModule
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918.Actors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SeedTransport

/-!
# Excluding the original M22 component

The previously proved native placement puts L₁ in K. The original seed
commutator relation therefore gives Ũ_H=[Ũ_H,K*]. Genuine F.9 geometry
constructs the quadratic actor in the original edge core. The strict native
M22 non-FF bound proves that the whole moved module belongs to Irr⁺; its
literal central quotient is then the code module by the native classification.
The original two-dimensional seed embeds into that quotient, contradicting
the one-dimensional fixed space of the actual marked parabolic radical.

All selection, movement and recognition premises are discharged from the
published SourceContext. This proves the M22 exclusion in both local quotient
cases, with no extra F.9.18 or B.4 callback. It does not use or assert W=U in
the distinct higher-field external-component argument. The six-cover and
higher-field branches remain with qt-d-138-fields-source; qt-d-1381-source
supplies the preceding source assumptions.
Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973),
using F.9.16 and the strict-section argument of F.9.18(7).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
open SourceCompletion LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Components.Swapped.LinearTwo.ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The literal component quotient cannot be M22 in the original local setup. -/
theorem source_no_mathieu (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) := by
  rintro ⟨eK⟩
  have hH := c.component.local_overgroup
  have hF9 := c.f9 H hH
  let : IsElementaryAbelian 2 (Source.UH H V₃) := c.localSetup.uh_elementary hH
  obtain ⟨star,B,_,hq⟩ := F918.exists_edge_quadratic_actor c.localSetup hF9
  let raw : LinearThree.SourceAction H V₃ V₁ := {
    line_le := c.localSetup.line_le_uh H
    seed_le := hF9.plus_le_H
    representation := SolvableExclusion.Three.Supercritical.Offenders.linearAction star
    conjugation := star.conjugation }
  let act : Mathieu.SourceAction H V₃ V₁ := {
    representation := raw.representation
    conjugation := raw.conjugation }
  let s := sourceMathieuSetup c eK
  have ho := Mathieu.Recognition.F918Source.component_orbit s
  have hgen : H = conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) := by
    rw [ho]
    simpa only [sup_assoc] using c.component.generated.symm
  have hfull : subspaceCommutator act.representation ⊤ (Source.starImage H K) = ⊤ := by
    have hh := source_moved_eq_top H V₃ V₁ act.representation (act.isSourceAction H V₃ V₁)
      K (one L T V₁) (T : Subgroup G) hgen
      (ho.symm ▸ source_mathieu_containment c eK)
      (Section07.ModelExclusions.point_residual_normalizes_seed (localNaturalSetup c.localSetup))
      (c.localSetup.line_le_plane.trans c.localSetup.plane_le_seed)
      (by
        rw [commutator_comm,
          Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup c.localSetup)]
        exact le_sup_left)
    rwa [ho] at hh
  have hf : Function.Injective act.representation :=
    f9_section_faithful _ hF9 (Comparison.sourceSection raw hF9.H_centralizes)
  have he := Mathieu.Recognition.F918Source.source_structure s
  have hn : ¬ Source.starImage H K ≤ act.representation.ker := by
    intro hk
    have hb : Source.starImage H K = ⊥ := by
      apply bot_unique
      intro k hkK
      exact hf ((hk hkK).trans (map_one act.representation).symm)
    have hh := Mathieu.Recognition.F918Source.component_nonabelian s
    rw [hb] at hh
    exact hh inferInstance
  have hi : IsIrrPlus act.representation (Source.starImage H K) ⊤ := by
    have hh := Mathieu.Recognition.NativeSource.whole_isIrrPlus
      (Mathieu.Recognition.F918Source.fittingCoordinates s) act.representation
      (Mathieu.Recognition.F918Source.source_sqtk c.component.sqtk)
      (by rwa [he.1]) (by rwa [he.1]) (Source.starImage H B) hq.1 hq.2.1 hq.2.2
    rwa [he.1] at hh
  have hcode := Mathieu.Recognition.F918Source.central_code s act c.component.sqtk
    Mathieu.Recognition.NativeSource.smallQuadraticCode (⊤ : Subrepresentation act.representation)
    hi (Source.starImage H B) hq.1 hq.2.1 hq.2.2
  exact source_mathieu_central_code_false c eK act ⊤ hfull.symm hcode
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
