module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Fusion
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Closure
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Kernels
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedCentralizers

/-!
# Conditional assembly of the pure-vector conclusions

The actual chosen-module normalizer equality connects the H.9 orbit
calculation to fusion. The two-core argument supplies abelian closure;
the existing A.1.7 application then centralizes every intersecting conjugate.

The centralizer orders, ambient pure-point Sylows and two-core control
remain explicit inputs. The source marking now supplies the summand
kernel facts. The remaining source constructions must be discharged
before this is a proof of 12.1.4--6.
Source: Aschbacher--Smith, printed pp.790--792.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The marked pure point has the original C_T(w) as Sylow in C_M(w).
The upgrade from C_M(w) to C_G(w) is the remaining 12.1.4--5 obligation. -/
theorem doubleNatural_relative_pure_sylow_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      w ≠ 1 → ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G))
        (normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix
  let M := normalizer (L : Set G)
  let P : Sylow 2 M := T.subtype D.sylow_normalizes_component
  have hP := S.pure_sylow_preimage P w hw hp hfix
  have hs := (Chapter1.IsSylowIn.map_iff M.subtype M.subtype_injective).mpr hP
  rw [map_inf _ _ _ M.subtype_injective] at hs
  have hPM : (P : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le D.sylow_normalizes_component
  rw [hPM, subgroupOf_map_subtype] at hs
  rw [inf_comm (centralizer ({(w : G)} : Set G)) M, ← inf_assoc] at hs
  have hTM : (T : Subgroup G) ⊓ M = (T : Subgroup G) :=
    inf_eq_left.mpr D.sylow_normalizes_component
  rw [hTM] at hs
  exact hs

/-- The actual chosen-module consumer of the four local pure-vector inputs.
All extra source premises remain visible until their independent proofs finish. -/
theorem doubleNatural_pure_conclusions_of_local_inputs_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.CentralizerOrders → B.PurePointSylows →
      B.SummandCentralizers → B.PureCoreControl →
      B.PureFusion ∧ B.PureCentralizerClosureAbelian ∧ B.PureIntersectionCentralizes := by
  let := D.doubledOrbit_elementary h
  intro S ho hs hd hc
  have hf := B.pureFusion_of_centralizerOrders S
    (D.doubledOrbit_normalizer_eq h B.orbit_eq) ho
  have ha := B.pureCentralizerClosureAbelian_of_core hs hd hc
  exact ⟨hf, ha, B.pureIntersectionCentralizes_of_fusion_of_abelianClosure hf ha⟩

/-- The original action marking discharges both summand-kernel premises.
Only the ambient Sylow/order argument and the local core argument remain. -/
theorem doubleNatural_pure_conclusions_of_orders_and_core_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.CentralizerOrders → B.PurePointSylows → B.PureCoreControl →
      B.PureFusion ∧ B.PureCentralizerClosureAbelian ∧ B.PureIntersectionCentralizes := by
  let := D.doubledOrbit_elementary h
  intro S ho hs hc
  exact D.doubleNatural_pure_conclusions_of_local_inputs_of_many h hmany B S ho hs
    (S.summandCentralizers (D.doubledOrbit_normalizer_eq h B.orbit_eq)) hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
