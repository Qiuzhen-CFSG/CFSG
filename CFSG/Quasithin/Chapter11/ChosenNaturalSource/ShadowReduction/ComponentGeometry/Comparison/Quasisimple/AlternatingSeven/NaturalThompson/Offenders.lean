module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.Natural
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.NaturalOuter
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.NonsplitOffenders.Symplectic.Transport
public import Theory.Representation.G2NaturalNormalizerOffenders

/-!
# Offender control for the three marked natural actions

For SL3, semilinearity and the odd-degree calculation reduce an outer
actor to even field degree; its fixed codimension exceeds its rank.
For Sp4, the proved field-involution centralizer bound discharges the
natural-normalizer transport. The G2 normalizer theorem supplies the
third row. All three conclusions refer to the supplied group isomorphism
and binary intertwiner, with relative normality of the actual layer.

These are the B.4.2(2)--(4) inputs to the original Thompson containment
at the end of 11.4.2, Aschbacher--Smith, printed pp.86 and777.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
variable {Q W : Type*} [Group Q] [Finite Q] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (ρ : Representation (ZMod 2) Q W) (A : Subgroup Q) [A.Normal]
  (F : BinaryField)

/-- Every offender in a faithful natural SL3 extension lies in the marked layer. -/
theorem linear_offender_le
    (e : ActionEquiv (ρ.comp A.subtype) (linearNatural F 3))
    (hf : Function.Injective ρ) {B : Subgroup Q} (hB : IsOffender ρ B) : B ≤ A := by
  by_cases ho : Odd F.degree
  · exact ChapterK.Linear.Natural.elementary_le_of_odd_degree ρ A hf F ho e hB.1
  · obtain ⟨s, hs⟩ := (Nat.even_or_odd F.degree).resolve_right ho
    have hd : F.degree = 2 * s := by omega
    have hp : 0 < s := by have := F.degree_pos; omega
    by_contra hn
    have hsem := ChapterK.Linear.Recognition.SourceFF.semilinear_of_natural e
    exact (not_lt_of_ge hB.2) (ChapterK.Linear.Natural.FieldActors.outer_elementary_bound
      ρ A F e hf hsem hB.1 hn s hp hd)

omit [FiniteDimensional (ZMod 2) W] in
/-- The symplectic row, including the actual outer-centralizer estimate. -/
theorem symplectic_offender_le (hF : 1 < F.degree)
    (e : ActionEquiv (ρ.comp A.subtype)
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))
    (hf : Function.Injective ρ) {B : Subgroup Q} (hB : IsOffender ρ B) : B ≤ A := by
  apply IrreducibleBranch.Symplectic.offender_le_natural_component_of_centralizer_bound
    ρ hf A F hF e ?_ hB
  intro a ha hout
  have hb := (ChapterK.Symplectic.Natural.outer_involution_centralizer_bound
    F.card_eq hF a ha hout).2
  omega

omit [Finite Q] [FiniteDimensional (ZMod 2) W] in
/-- The G2 row preserves the natural octonion-quotient marking. -/
theorem g2_offender_le (hF : 1 < F.degree)
    (e : ActionEquiv (ρ.comp A.subtype)
      (restrictScalars (k := ZMod 2) (g2Natural F.Carrier)))
    (hf : Function.Injective ρ) {B : Subgroup Q} (hB : IsOffender ρ B) : B ≤ A := by
  rcases F with @⟨K, hField, hFinite, hChar, hAlg, n, hn, hcard⟩
  have hAlgEq : hAlg = ZMod.algebra K 2 := Subsingleton.elim _ _
  subst hAlg
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  exact Atlas.G2.Natural.Normalizer.ambient_offender_le K ρ A e.groupEquiv e.linearEquiv
    (fun g v => e.intertwines g v) hf (by change 1 < n at hF; omega) hcard hB

/-- The supplied SL3, Sp4 or G2 marking controls offenders in any faithful
ambient extension of its actual image. -/
theorem coordinate_offender_le {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}
    (c : LocalGeometry.Coordinates D F) (hF : 1 < F.degree)
    (e : ActionEquiv (ρ.comp A.subtype) (restrictScalars (k := ZMod 2) c.modelAction))
    (hf : Function.Injective ρ) {B : Subgroup Q} (hB : IsOffender ρ B) : B ≤ A := by
  cases c with
  | sl3 m => exact linear_offender_le ρ A F e hf hB
  | sp4 m => exact symplectic_offender_le ρ A F hF e hf hB
  | g2 m => exact g2_offender_le ρ A F hF e hf hB

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
