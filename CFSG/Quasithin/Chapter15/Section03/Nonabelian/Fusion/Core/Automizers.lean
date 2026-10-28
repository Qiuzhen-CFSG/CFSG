module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Reduction
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.LocalCore
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models

/-!
# Automizer assembly for 15.3.59

The first three source clauses and the genuine earlier s = 1 actions imply
O²(M) = Y. The tensor coordinates on V and the direct sum coordinates on
P/V share one actual actor I → SL₂(2) × SL₂(2), where I = YU and P = O₂(I).
They identify P with O₂(Y), compute the orders needed by `LocalCore`, and
identify V with [P,P] using V = Z(P). The actual Sylow subgroup and natural
action of M then give O₂(YT) = O₂(Y). Relative normality transfers this to
O₂(M), and the earlier characteristic-two condition gives F*(M) = O₂(M).

For both literal conjugation layers, `Models` proves that the Y-image is
the two-residual of its full automorphism normalizer. The central-derived
identity matches the two images, and `Reduction` descends through the
coprime two-layer kernel to obtain the final residual equality.

The source-facing theorem `residual_eq_of_first_three_and_s1_actions`
assumes neither the local core equality, the automizer identities, M = YT,
nor O²(M) = Y. Its explicit earlier-source inputs are relative normality
of Y in M, two-perfectness of Y, characteristic two in M, C_Y(V) = O₂(Y),
the natural action of M, the common s = 1 actor with its exact kernel and
Y-image, both compatible module coordinates, and V = Z(P).
The first three clauses of 15.3.59 are also explicit inputs. The parent
`Core` assembly must supply these source witnesses; it can then use
`Core.supplement_of_residual` for the actual subgroup product and factors.
This conditional deduction is not an assertion of all of 15.3.59.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.53(1), 15.3.54(4), 15.3.55, 15.3.58 and proof of 15.3.59,
printed pp.1146–1150, especially the final paragraph on p.1150.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers
open Subgroup

variable {G : Type*} [Group G] [Finite G]
variable (T : Sylow 2 G) (M Y I P V Z ZS : Subgroup G)
variable (hTM : (T : Subgroup G) ≤ M)
variable (hI : I = Y ⊔ Nonabelian.closureU Z ZS) (hIM : I ≤ M)
variable (hMY : M ≤ normalizer (Y : Set G))
variable (hP : P = Stellmacher.twoCoreAmbient I) (hVP : V ≤ P)
variable {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
variable [(V.subgroupOf P).Normal]
variable (d : Models.LayerActions I Y P V hIP hIV)
variable (a : NaturalOrthogonalAction M V)
variable (hcentral : Y ⊓ centralizer (V : Set G) = Stellmacher.twoCoreAmbient Y)
variable (hfirst : Nonabelian.closureU Z ZS = Nonabelian.coreQ Z ∧
  (∃ S : Sylow 2 (Y ⊔ Nonabelian.closureU Z ZS : Subgroup G),
    (S : Subgroup (Y ⊔ Nonabelian.closureU Z ZS : Subgroup G)).map
      (Y ⊔ Nonabelian.closureU Z ZS).subtype =
        Nonabelian.residualSylow (T : Subgroup G) Z) ∧
  ((Nonabelian.residualSylow (T : Subgroup G) Z).subgroupOf
    (T : Subgroup G)).index = 2)

include hTM hI hIM hMY hP hVP d a hcentral hfirst

/-- The first three clauses of 15.3.59 and the actual s = 1 actions give
O₂(YT) = O₂(Y). All numerical premises of the local-core calculation are
discharged from the two module coordinates and their common actor. -/
theorem local_core_eq_of_first_three_and_s1_actions :
    Stellmacher.twoCoreAmbient (Y ⊔ (T : Subgroup G)) = Stellmacher.twoCoreAmbient Y := by
  have hYI : Y ≤ I := hI.symm ▸ le_sup_left
  have hPY := d.core_eq_twoCore_Y hYI (hIM.trans hMY) hVP hP
  have hQcard : Nat.card (Stellmacher.twoCoreAmbient Y) = 256 := by
    rw [← hPY]
    exact d.card_core hVP
  have hpart : 2 ^ (Nat.card (Y ⊔ Nonabelian.closureU Z ZS : Subgroup G)).factorization 2 =
      1024 := by
    rw [← hI]
    exact d.twoPart_actor_domain (hP ▸ map_subtype_le _) hVP
  exact LocalCore.core_eq_of_first_three T M Y V Z ZS hTM (hYI.trans hIM) hMY a
    hcentral hQcard (d.card_Y_quotient hYI (hIM.trans hMY) hVP hP) hpart hfirst

/-- The computed supplement core and the earlier characteristic-two condition
identify both the two-core and the actual generalized Fitting subgroup of M. -/
theorem core_and_fitting_eq_of_first_three_and_s1_actions
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) :
    Stellmacher.twoCoreAmbient M = Stellmacher.twoCoreAmbient Y ∧
      (Theory.GroupTheory.generalizedFitting M).map M.subtype =
        Stellmacher.twoCoreAmbient Y := by
  have hYM : Y ≤ M := (hI.symm ▸ le_sup_left).trans hIM
  have hlocal := local_core_eq_of_first_three_and_s1_actions
    T M Y I P V Z ZS hTM hI hIM hMY hP hVP d a hcentral hfirst
  exact ⟨core_eq_of_supplement_core T M Y hTM hYM hMY hlocal,
    fitting_eq_of_supplement_core T M Y hTM hYM hMY hlocal hchar⟩

/-- The final two-layer deduction in 15.3.59. The premises are the first
three source clauses and genuine earlier local data: relative normality,
two-perfectness of Y, characteristic two in M, the natural action of M,
the common s = 1 actor and coordinates, and V = Z(P). The local core
identity, V = [P,P], both full automizer-normalizer residual identities,
and matching of the two actions are proved, not assumed. -/
theorem residual_eq_of_first_three_and_s1_actions
    (hY : IsPPerfect 2 Y)
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hcenter : V = (center P).map P.subtype) :
    Stellmacher.twoResidualAmbient M = Y := by
  have hYI : Y ≤ I := hI.symm ▸ le_sup_left
  have hPY : P = Stellmacher.twoCoreAmbient Y :=
    d.core_eq_twoCore_Y hYI (hIM.trans hMY) hVP hP
  have hMP : M ≤ normalizer (P : Set G) := by
    rw [hPY]
    exact hMY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hlocal : Stellmacher.twoCoreAmbient (Y ⊔ (T : Subgroup G)) = P :=
    (local_core_eq_of_first_three_and_s1_actions
      T M Y I P V Z ZS hTM hI hIM hMY hP hVP d a hcentral hfirst).trans hPY.symm
  have hlower : IsNormalizerResidual (lowerImage M Y V a.normalizes) :=
    d.lower_normalizer_residual M hYI hIM a.normalizes
  have hupper : IsNormalizerResidual (upperImage M Y P V hMP a.normalizes) :=
    d.upper_normalizer_residual M hYI hIM hMP a.normalizes
  exact residual_eq_of_local_core_and_automizers T M Y P V hTM (hYI.trans hIM) hMY hY
    hPY hMP a.normalizes hVP hlocal hchar
    (Models.LayerActions.lower_central hcenter) (d.lower_eq_derived hVP hcenter).le
    hlower hupper

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers
