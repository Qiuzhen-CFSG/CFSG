module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Inputs

/-!
# The seed-join two-core lies in the component stabilizer

Put Q = O₂(XT). It lies in T and is normalized by T. If Q is outside T₁,
the local commutator calculation gives X = [X,Q] ≤ Q, contradicting the
odd part of X. This proves the core bound consumed by the original
diagonal centralizer argument, with the local calculation still explicit.

Source: Aschbacher--Smith 10.2.11(1--2), printed p.753.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G} {c : Configuration s a b}

/-- The first SeedAnalysis field follows from the local commutator calculation. -/
theorem core_bound (h : LocalCalculation c) :
    (centralizerSeed T L (a*b) ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  let X := centralizerSeed T L (a*b)
  let J := X ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := by
    have he := pCoreIn_le_sylow J (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
    change Q ≤ ((T : Subgroup G).subgroupOf J).map J.subtype at he
    rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)] at he
  have hJQ : J ≤ normalizer (Q : Set G) := by
    simpa only [Q, pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 J).le_normalizer_map J.subtype
  by_contra hout
  have he : ⁅X,Q⁆ = X := h.commutator Q hQT (le_sup_right.trans hJQ) hout
  have hXQ : X ≤ Q := by
    rw [← he]
    exact le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hJQ)
  exact h.not_two ((isPGroup_pCoreIn 2 J).to_le hXQ)

/-- Actual application to the central-core conclusion of 10.2.11(1). -/
theorem span_central_core (h : LocalCalculation c) :
    centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2) :=
  c.span_central_core_of_seedJoin_core (core_bound h)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed
