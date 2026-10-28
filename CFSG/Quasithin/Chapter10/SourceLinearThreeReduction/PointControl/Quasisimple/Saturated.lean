module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Preparation
public import Theory.Representation.BinaryConjugationSection.SaturatedFixer
public import Theory.GroupAction.PerfectCentralQuotient
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion
/-!
# Applying the saturated-section argument to the actual point component

The opposite moved factor is elementary, normalizes I and centralizes L.
The reduced coordinates on the original moved subgroup therefore apply
the rank-saturation theorem directly. Faithful descent through I/Z(I)
transfers concrete model bounds to Aut(I), and the source moved-normalizer
bound contradicts the resulting common centralization.

Source: Aschbacher--Smith 10.2.9, printed pp.750--751. Other.SixDimensional
uses this on the literal natural-plus-dual row, including fixed vectors.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02 Representation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The actual opposite moved factor centralizes the containing component. -/
theorem common_centralizer_of_saturated_section
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) L W}
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) ρ)
    {m : ℕ} (hc : 2^m ≤ Nat.card W) (hr : primeRank 2 (MulAut I) ≤ m) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G) := by
  let := source_original_full_moved_elementary D
  let U := (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  exact d.centralizes_of_saturated_automorphism_rank c.strict.le
    (partner_normalizes D c) c.crossed hc hr

/-- A model automorphism bound excludes the actual escaping component. -/
theorem not_of_saturated_section [Group.IsPerfect I]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) L W}
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) ρ)
    {m : ℕ} (hc : 2^m ≤ Nat.card W)
    {H : Type*} [Group H] [Finite H] (e : (I ⧸ center I) ≃* H)
    (hr : primeRank 2 (MulAut H) ≤ m) : False := by
  have hI := (Theory.GroupTheory.primeRank_le_of_injective 2 (MulAut.centralQuotientAction e)
    (MulAut.centralQuotientAction_injective e)).trans hr
  exact source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer
    I c.escapes (common_centralizer_of_saturated_section D c d hc hI)
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
