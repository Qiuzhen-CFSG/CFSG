module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.Radical.Geometry
public import Theory.SpecificGroups.PSL3.PointRadicalGeneration.ParabolicCore

/-!
# The actual starred point-parabolic radical in G.2.5

The full point-parabolic core and minimality calculations identify the actual
matrix image of U* with the transvection radical. The existing quotient
transports then give U* = O₂(N_L(V₁)*) and explicit additive F² coordinates,
hence |U*| = 2^(2n). The field characteristic is deduced from the source field
cardinality, including n = 1.

Only the source inputs U ≤ T, Φ(U) ≤ V₁ and U* ≤ L* remain explicit. These
are the G.2.2 premises and linear-image input retained by the source assembly;
no model core, minimality or generation premise remains in these conclusions.
The independent three-point generation argument is assembled by the parent.

Source: Aschbacher–Smith, G.2.5(1), printed pp.335–336, using the full-normalizer
argument of G.2.3, printed pp.333–334.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open Setup Matrix.PSL3.PointRadicalGeneration
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G]
variable {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)

include d

/-- The actual U* image is the whole concrete point radical. -/
theorem pointRadicalImage_eq_radical (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUL : D.star D.U ≤ D.star D.L) :
    d.pointRadicalImage = radical d.point :=
  d.pointRadicalImage_eq_of_minimality hUT hf hUL (radical_minimal d.point d.point_dimension)

/-- G.2.5(1): U* is the two-core of the full starred setwise point normalizer. -/
theorem star_U_eq_pointNormalizer_core (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUL : D.star D.U ≤ D.star D.L) :
    D.star D.U = (D.star (D.L ⊓ D.G₁)).pCoreIn 2 := by
  let := d.radical_field_char_two
  exact d.star_U_eq_core_of_point_model_facts hUT hf hUL
    (radical_minimal d.point d.point_dimension) (parabolic_twoCore_eq d.point d.point_dimension)

/-- Explicit F² coordinates for the original starred U, using the supplied SL₃ model. -/
noncomputable def starUPointRadicalEquiv (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUL : D.star D.U ≤ D.star D.L) :
    D.star D.U ≃* Multiplicative (Fin 2 → F) :=
  d.starUEquivOfMinimality hUT hf hUL (radical_minimal d.point d.point_dimension)

/-- The order assertion for U* in G.2.5(1), with no model minimality premise. -/
theorem card_star_U_point_radical (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUL : D.star D.U ≤ D.star D.L) :
    Nat.card (D.star D.U) = 2 ^ (2 * n) :=
  d.card_star_U_of_minimality hUT hf hUL (radical_minimal d.point d.point_dimension)

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree
