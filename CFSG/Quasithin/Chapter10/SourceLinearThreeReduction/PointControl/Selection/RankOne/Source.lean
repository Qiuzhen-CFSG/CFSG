module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.Orbits
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.Normalizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.Source

/-!
# Rank-one geometry with its remaining fixed-layer premise

The actual natural quotient supplies every Baumann fixed orbit, and the
rank-one minimal parabolic supplies Baumann normalizer control. This assembly
retains the additional assertion that T₁ fixes the full L₀-fixed layer.
That assertion is not supplied by the natural-cover marking: normalizing
field actors can move its central kernel. It still requires an ambient
source proof before RankOneGeometryAt, and hence the selection, is complete.

The final theorem applies this conditional geometry to the literal selection
consumer. Source: Aschbacher--Smith, 10.1.1--2 and 10.2.1,9, pp.741--742,750.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Both geometry fields beyond full fixed-layer centralization are discharged. -/
theorem point_geometry_of_fixed_layer
    (hnotA5 : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : RankOneNatural D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≤
      centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G)) :
    RankOnePointGeometry D t := by
  refine ⟨hfix, baumann_normalizer_le D hnotA5 hmodel (fun hn => htn (hn ht)), ?_⟩
  intro v hv _ _ _
  exact partner_baumann_conjugate_fixed_of_rankOneNatural D hmodel ht hv

omit D in
/-- The exact remaining fixed-layer obligation, with every permitted source input. -/
@[expose] def FixedLayerAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule → D.fullModule = D.moduleSubgroup →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) → RankOneNatural D →
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) →
    ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) →
      HalfSylowUnique D →
      D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≤
        centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G)

omit D in
/-- Conditional assembly; the fixed-layer obligation remains to be proved. -/
theorem rankOneGeometryAt_of_fixed_layer (hfixed : FixedLayerAt T) :
    RankOneGeometryAt T := by
  intro hmany L D hminimal hfull hnotA5 hmodel hJ t ht htn hcross hhalf
  exact point_geometry_of_fixed_layer D hnotA5 hmodel ht htn
    (hfixed hmany L D hminimal hfull hnotA5 hmodel hJ t ht htn hcross hhalf)

omit D in
/-- Literal application to the existing selection assembly, retaining its other owners. -/
theorem selectionAt_of_fixed_layer
    (hchoice : ModuleChoiceAt T) (hfixed : FixedLayerAt T)
    (hthree : BinaryThreeGeometryAt T) : SelectionAt T :=
  selectionAt_of_source_geometry hchoice (rankOneGeometryAt_of_fixed_layer hfixed) hthree

end CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
