module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.OddDegree.CubicScalar
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.OddDegree.Sylow

/-!
# Odd degree and the original Sylow placement

The cubic obstruction excludes even field degree. Applying the odd-degree
normalizer theorem and the corrected cohomology identity gives D=D₀,
T=T_L, C_T(L)=1, O₂(LT)=V, and the actual Sylow subgroup of L mapping to T.
The established quotient calculation now gives the literal elementary T/P
of order q² with no remaining parity or Sylow-placement premise.

This completes the paragraph from “Assume n is even” through the Sylow
placement on printed p.774 of Aschbacher--Smith. Earlier source data remain
in OrthogonalInput, to be constructed by the common-core assembly. Relative
component recognition and the subsequent orthogonal marking are separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)
include d

/-- The full Hall group is the extracted D₀ on the original source input. -/
theorem source_hall_eq_oddCartanPart : oddCartanPart A = A :=
  source_oddCartanPart_eq d (source_degree_odd d)

/-- The source containment D≤X now holds for the whole original Hall group. -/
theorem source_hall_le_cartan : A ≤ X := by
  rw [←source_hall_eq_oddCartanPart d]
  exact d.oddCartan_le

/-- The original T is Sylow in L, with its literal ambient image. -/
theorem source_original_sylow_placement :
    sourceTL T L = (T : Subgroup G) ∧ (T : Subgroup G) ≤ L ∧
      ∃ t : Sylow 2 L, (t : Subgroup L).map L.subtype = (T : Subgroup G) :=
  source_sylow_of_odd d (source_degree_odd d)

/-- The cohomology conclusion and characteristic-two normalizer placement,
with the original equality T=T_L proved rather than assumed. -/
theorem source_original_sylow_and_normalizer :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
      (L ⊔ (T : Subgroup G)).pCoreIn 2 = V ∧
      (T : Subgroup G) ≤ L ∧
      (∃ t : Sylow 2 L, (t : Subgroup L).map L.subtype = (T : Subgroup G)) ∧
      coreNormalizer V H h ∈ Chapter1.He G ∧
      orthogonalJoin (f.Li 1) V h ≤ coreNormalizer V H h ∧
      ((pairCore V H h).subgroupOf (orthogonalJoin (f.Li 1) V h)).Normal :=
  source_sylow_and_normalizer d (source_original_sylow_placement d).1

/-- The exact quotient required by the following component argument, with
no additional parity, containment or quotient-geometry hypothesis. -/
theorem source_original_sylow_quotient :
    let := source_pairCore_normal_sylow d
    IsElementaryAbelian 2 ((T : Subgroup G) ⧸ (pairCore V H h).subgroupOf T) ∧
      Nat.card ((T : Subgroup G) ⧸ (pairCore V H h).subgroupOf T) =
        (2 ^ S.field.degree) ^ 2 :=
  source_sylow_quotient_of_odd d (source_degree_odd d)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
