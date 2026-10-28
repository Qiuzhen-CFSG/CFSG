module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankOneBender
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# The cubic radical forced by the original condition (*)

The residual image lies in the normal two-by-three preimage in the literal
centralizer of the marked module image in X-hat. Its order is divisible by three.
Consequently that centralizer's solvable radical has order divisible by
three, without a rank-two or faithful E9 assumption. This is the obstruction
used in the remaining rank-one model inspection of 12.6.26.

Source: Aschbacher--Smith, proof of 12.6.26, printed pp.832--833.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)

include hz hTV hTz hbound hH hn a in
/-- Condition (*) forces a cubic divisor in the exact centralizer radical. -/
theorem SourceHypothesis.original_action_centralizer_radical_three_dvd :
    let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
    let C := centralizer (U : Set a.action.range)
    3 ∣ Nat.card (solvableRadical C) := by
  let A₀ := ((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action
  let A := A₀.subgroupOf a.action.range
  let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
  let C := centralizer (U : Set a.action.range)
  have hAC : A ≤ C := by
    intro x hx u hu
    exact Subtype.ext (a.residual_centralizes hx u.val hu)
  let q := QuotientGroup.mk' (pCore 2 C)
  let N := (pCore 3 (C ⧸ pCore 2 C)).comap q
  let : Group.IsNilpotent (pCore 2 C) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsNilpotent (pCore 3 (C ⧸ pCore 2 C)) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable N := isSolvable_comap_of_solvable_ker q _
  have hAR : A.subgroupOf C ≤ solvableRadical C :=
    (S.original_action_residual_le_centralizer_twoThreeCore D hZ z hz hTV hTz
      hbound hH hn c a).trans (le_solvableRadical N inferInstance inferInstance)
  have hd : 3 ∣ Nat.card (A.subgroupOf C) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (show A₀ ≤ a.action.range from map_le_range _ _)).toEquiv]
    exact a.residual_three_dvd
  exact hd.trans (card_dvd_of_le hAR)

end CFSG.Quasithin.Chapter12.Section06
