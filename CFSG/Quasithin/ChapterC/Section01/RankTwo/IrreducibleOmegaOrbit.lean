module
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.CentralOrbit

/-!
# Irreducible subgroups in the Sylow omega orbit

The normal closure of the omega center of a Sylow subgroup is reduced in
characteristic two. Any irreducible invariant subgroup containing that omega
center lies in its normal closure. A perfect-commutator identity then transfers
movement of this closure to the Thompson subgroup.

These are the structural steps used in Aschbacher–Smith, source 9.3.6–9.3.7.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.MSCentralOrbit
variable {H : Type*} [Group H] [Finite H]

theorem omegaOrbit_reduced (P : Sylow 2 H)
    (hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H) :
    IsPReduced 2 (omegaOrbit (P : Subgroup H)) :=
  omegaCenter_normalClosure_reduced P hchar

theorem irreducible_le_omegaOrbit (R U A : Subgroup H)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hOmega : omegaCenterIn R ≤ U)
    (hAU : A ≤ normalizer (U : Set H))
    (hirr : ∀ N : Subgroup H, N ≤ U → A ≤ normalizer (N : Set H) →
      N = ⊥ ∨ N = U) : U ≤ omegaOrbit R := by
  let W := omegaOrbit R
  have hOmegaN : omegaCenterIn R ≠ ⊥ := by
    intro h
    exact inf_omegaCenterIn_ne_bot_of_normalized_twoGroup R R le_rfl hp
      R.le_normalizer hne (by rw [h,inf_bot_eq])
  have hne' : U ⊓ W ≠ ⊥ := by
    intro h
    exact hOmegaN (bot_unique ((le_inf hOmega subset_normalClosure).trans_eq h))
  have hAW : A ≤ normalizer (W : Set H) := le_normalizer_of_normal
  exact ((hirr (U ⊓ W) inf_le_left
    ((le_inf hAU hAW).trans inf_normalizer_le_normalizer_inf)).resolve_left hne') ▸ inf_le_right

omit [Finite H] in
theorem thompson_moves_of_component_commutator (R : Subgroup H)
    (B W : Subgroup H) [W.Normal]
    (hB : B = ⁅B,elementaryAbelianMaxJ R⁆)
    (hmove : ¬ B ≤ centralizer (W : Set H)) :
    ¬ elementaryAbelianMaxJ R ≤ centralizer (W : Set H) := by
  intro hJ
  apply hmove
  rw [hB]
  exact (commutator_mono le_rfl hJ).trans (commutator_le_right _ _)
end CFSG.Quasithin.ChapterC.MSCentralOrbit
