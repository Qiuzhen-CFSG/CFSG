module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Nonfusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource

/-!
# Ambient separation of the original unitary involution types

The actual Chapter12 chosen module supplies W=wholeReduced T L. The prepared
unitary comparison constructs Hermitian coordinates on its original O₂(L),
and ambient conjugacy preserves the singular locus. The two explicit
Hermitian types therefore give nonconjugate involutions in the original G.
Ordinary and degree-two comparisons, both orientations, and the full
KnownSimple hypotheses are retained.

Source: Aschbacher–Smith F.4.35 and 5.3.3, printed pp.292,659
(`refs/quasithin.pdf`). The remaining realization, outer-transfer,
short-root-centralizer and full-extension-order steps are separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Original-module coordinates retain both the quotient action and ambient
nonfusion of the singular and nonsingular Hermitian types. -/
theorem rankOne_unitary_hermitian_fusion
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m) [NeZero m]
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm) :
    ∃ (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field m))
      (f : L.pCoreIn 2 ≃* Multiplicative (Space m)),
      (∀ (l : L) (v : L.pCoreIn 2),
        (f.symm (Multiplicative.ofAdd (action m (e (QuotientGroup.mk' (pCore 2 L) l))
          (f v).toAdd)) : G) = (l : G)*(v : G)*(l : G)⁻¹) ∧
      ∀ x y : L.pCoreIn 2, IsConj (x : G) (y : G) →
        (form m (f x).toAdd = 0 ↔ form m (f y).toAdd = 0) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_hermitian_fusion hi hH hp m hm hc

/-- Both Hermitian involution types survive as distinct conjugacy classes in G. -/
theorem rankOne_unitary_core_two_nonconjugate_involutions
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm) :
    ∃ x ∈ L.pCoreIn 2, ∃ y ∈ L.pCoreIn 2,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_core_two_nonconjugate_involutions hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
