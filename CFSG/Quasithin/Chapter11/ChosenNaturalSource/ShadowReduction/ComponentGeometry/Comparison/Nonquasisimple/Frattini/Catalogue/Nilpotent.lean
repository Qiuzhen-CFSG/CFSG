module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Catalogue.FiveSupplement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini

/-!
# Excluding the nilpotent-extension catalogue row on the chosen flag

The actual seed is nontrivial and perfect. In the nilpotent SL₂(5) row
it therefore supplements the literal two-Fitting preimage, by the preceding
SL₂(5) calculation. Fitting centralization and seed centralization then
make Kz centralize the line, contradicting strict comparison.

Fitting centralization remains with the same task's canonical-radical
argument; it is not inferred from the extension model.
Source: Aschbacher--Smith, 11.1.1 and 11.4.2, printed pp.761 and 777.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The nilpotent-extension row of the complete catalogue gives precisely
the excluded Fitting-times-seed factorization on the actual flag. -/
theorem ofFlag_fitting_seed_split_of_nilpotent_extension (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G) (hA : f.Li 0 ≠ ⊥)
    (hm : HasExtension ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
      (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
      (fun Q _ => Source.IsSL Q 2 5)) :
    (ofFlag S f X z H).Kz = fittingPreimage (ofFlag S f X z H) ⊔
      (ofFlag S f X z H).L₁ := by
  let E := ofFlag S f X z H
  have hle : E.L₁ ≤ E.Kz := le_conjugateSpanBy _ _
  let C := E.L₁.subgroupOf E.Kz
  let e : C ≃* E.L₁ := subgroupOfEquivOfLe hle
  let : Group.IsPerfect E.L₁ := LocalGeometry.localResidual_perfect _
  let : Nontrivial E.L₁ := (Subgroup.nontrivial_iff_ne_bot _).mpr hA
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Nontrivial C := e.surjective.nontrivial
  have hmodel := twoFitting_sl2_of_nilpotent_extension (by decide : 3 < 5) (by decide) hm
  have hh := congrArg (map E.Kz.subtype) (fitting_seed_split_of_sl2_five C hmodel)
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hle,
    ← MonoidHom.range_eq_map,range_subtype] at hh
  exact hh.symm

/-- Fitting centralization rules out the complete catalogue's nilpotent
extension row. This retains the literal extension model and actual seed. -/
theorem ofFlag_not_nilpotent_extension (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hF : fittingPreimage (ofFlag S f X z H) ≤ centralizer ((ofFlag S f X z H).V₁ : Set G)) :
    ¬ HasExtension ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
      (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
      (fun Q _ => Source.IsSL Q 2 5) := by
  intro hm
  exact not_fitting_seed_split_of_centralizes h hf hne hF
    (ofFlag_fitting_seed_split_of_nilpotent_extension S f X z H hA hm)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
