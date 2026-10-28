module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ActionQuotient
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.GroupTheory.CComponent.Basic
public import Stellmacher.ElementaryAbelianMaxJ
public import Theory.Representation.BinaryPermutation

/-!
# Common local notation for the characteristic-two branches

The planes are transported through the genuine natural orthogonal action.
All residuals, spans, intersections and action quotients below use the
constructions of Section 15.3. In particular `R` is a two-core, while `Y`
and the second choice of `Yplus` use two-residuals. The star quotient is
formed by the centralizer inside the outside overgroup.

`LocalData` records these choices only. The source hypotheses and the
conclusions of 15.3.2–12 must still be supplied explicitly in an application.
It asserts neither the existence of a component nor any classification or
characteristic-two exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1121–1126 and 1130–1134.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo

open Subgroup

variable {G : Type*} [Group G]

/-- Actual orthogonal coordinates and the choice in Hypothesis 15.3.10. -/
structure LocalData (G : Type*) [Group G] where
  T : Sylow 2 G
  M : Subgroup G
  Mc : Subgroup G
  sylow_le : (T : Subgroup G) ≤ M
  action : NaturalOrthogonalAction M (localModule T M)
  Yplus : Subgroup G
  choice : Hypothesis15310 M (residualY M Mc)
    (planeStabilizer T (action.plane 1)) (action.plane 1) Yplus

namespace LocalData

variable (d : LocalData G)

abbrev Z : Subgroup G := centralInvolutions d.T
abbrev V : Subgroup G := localModule d.T d.M
abbrev V₁ : Subgroup G := d.action.plane 1
abbrev V₂ : Subgroup G := d.action.plane (Multiplicative.ofAdd (1 : ZMod 2))
noncomputable abbrev Y : Subgroup G := residualY d.M d.Mc
abbrev S : Subgroup G := planeStabilizer d.T d.V₁
abbrev ZS : Subgroup G := fixedPlane d.V d.S
abbrev R : Subgroup G := (d.Yplus ⊔ d.S).pCoreIn 2
abbrev Hplus : Set (Subgroup G) := outsideFamily d.Yplus d.S d.M
abbrev HplusMinimal : Set (Subgroup G) := minimalOutsideFamily d.Yplus d.S d.M
abbrev MI (I : Subgroup G) : Subgroup G := d.M ⊓ I
abbrev UI (I : Subgroup G) : Subgroup G := localSpan d.Z I
abbrev Star (I : Subgroup G) := LocalActionQuotient d.Z I
abbrev starMap (I : Subgroup G) : I →* d.Star I := localActionMap d.Z I
abbrev starImage (I X : Subgroup G) : Subgroup (d.Star I) := localActionImage d.Z I X

/-- `U_L = [U_I,L]` in the rank-one branch. -/
abbrev componentModule (I L : Subgroup G) : Subgroup G := ⁅d.UI I, L⁆

/-- `W_L = ⟨V^L⟩` in the rank-two branch. -/
abbrev componentSpan (L : Subgroup G) : Subgroup G := localSpan d.V L

/-- The subgroup `S₀` in the final offender argument. -/
abbrev S0 (L : Subgroup G) : Subgroup G := d.S ⊓ (L ⊔ (L ⊔ d.S).pCoreIn 2)

end LocalData

/-- The equality being contradicted, using the genuine generalized Fitting
subgroup and the intrinsic two-core of `I`. -/
def HasCharacteristicTwo (I : Subgroup G) : Prop :=
  Theory.GroupTheory.generalizedFitting I = pCore 2 I

/-- The common output of 15.3.15(2) and 15.3.26(2). This is a witness
to be constructed, not a hypothesis in `LocalData`. The C-component
condition is internal to the actual Thompson subgroup of `I`. -/
structure ComponentWitness (d : LocalData G) (I : Subgroup G) where
  L : Subgroup G
  le_thompson : L ≤ Stellmacher.elementaryAbelianMaxJ I
  component : (L.subgroupOf (Stellmacher.elementaryAbelianMaxJ I)).IsCComponent
  outside : ¬ L ≤ d.M
  rank_pos : 1 ≤ primeRank 3 L
  commutator_eq : L = ⁅L, d.Yplus⁆
  star_quasisimple : Theory.GroupTheory.IsQuasisimple (d.starImage I L)
  core_quotient_quasisimple : Theory.GroupTheory.IsQuasisimple (L ⧸ pCore 2 L)

/-- The natural degree-eight binary module is the even-weight subspace
modulo constants, with its full coordinate permutation action. A compatible
identification with this module is the output needed from 15.3.32(1). -/
structure NaturalEightAction (I U : Subgroup G) where
  normalizes : I ≤ normalizer (U : Set G)
  coordinates : U ≃* Multiplicative (BinaryPermutation.natural (Fin 8))
  actor : I →* Equiv.Perm (Fin 8)
  onto : Function.Surjective actor
  compatible : ∀ (i : I) (u : U),
    coordinates (U.normalizerMonoidHom ⟨i, normalizes i.property⟩ u) =
      Multiplicative.ofAdd (BinaryPermutation.naturalRepresentation (Fin 8)
        (actor i) (Multiplicative.toAdd (coordinates u)))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo

end
