module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Pair
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Assembly

/-!
# Assembly of the literal centralizer geometry

The source fixed-space theorem makes the exchanged moved factors disjoint.
The p-group fixed-point theorem then supplies a nonidentity T-fixed vector
in their product. Its unique two coordinates are nonidentity and fixed by
N_T(L), and their product is the required central involution. The survivor's
point-centralizer bound controls C_{G_z}(V_z) directly. The independent
escape and two-core arguments supply the remaining fields.

This is a conditional source assembly, not a proof that its three earlier
inputs hold. It feeds the existing actual replacement construction with
the literal X=O²(C_{L₀}(z)), K_z and V_z from Contracts.

Source: Aschbacher--Smith 10.2.10--11 and 10.3.1--2, printed pp.753--756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Construct the actual centralizer data, including the chosen vectors,
from the three outstanding source arguments. -/
theorem centralizerGeometry_of_source_inputs
    (hfixed : FixedSpaceTIAt T) (hcore : CoreReducedAt T) (hescape : EscapeAt T) :
    CentralizerGeometryAt T := by
  intro hmany L D s
  obtain ⟨hz,hti⟩ := hfixed hmany L D s
  obtain ⟨a,b,ha,hb,hane,hbne,haf,hbf,hcentral,horder⟩ := exists_survivor_diagonal s hz
  obtain ⟨hfull,hreduced⟩ := hcore hmany L D s hz hti a b ha hb hane hbne
    haf hbf hcentral horder
  have hzV : a * b ∈ D.fullModule :=
    D.fullModule.mul_mem (survivor_moved_le s ha) (survivor_partner_le s hb)
  exact ⟨{
    first := a
    second := b
    first_mem := ha
    second_mem := hb
    first_ne := hane
    second_ne := hbne
    first_fixed := haf
    second_fixed := hbf
    fixed_part := hz
    moved_ti := hti
    central := hcentral
    order := horder
    escape := hescape hmany L D s hz hti (a*b) hzV hcentral horder
    full_core := hfull
    module_centralizer := centralizerModule_centralizer_le s ha hane
    reduced := hreduced }⟩

/-- The actual A₅ replacement consumer. Wreath recognition and overgroup
span are the independent inputs owned by the replacement assembly task. -/
theorem replacement_of_geometry_source_inputs
    (hfixed : FixedSpaceTIAt T) (hcore : CoreReducedAt T) (hescape : EscapeAt T)
    (hwreath : WreathRecognitionAt T) (hovergroups : OvergroupSpanAt T) :
    SourceLinearThreeReplacementAt T :=
  replacement_of_source_inputs
    (centralizerGeometry_of_source_inputs hfixed hcore hescape) hwreath hovergroups

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry
