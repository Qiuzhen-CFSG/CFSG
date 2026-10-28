module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Setup
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.InvariantFactor
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.Seeds

/-!
# The original action and residual comparisons for the repeated-natural row

The actual S₃-square quotient of KS gives a proper normal subgroup of its
two-residual above the two-core. Transporting through O²(KS)=K proves
S-reducibility on K/O₂(K). The earlier Kc centralization clause identifies
KI with Kc through the residual of the full plane centralizer.

Source: Aschbacher--Smith, 15.2.21(1) and 15.2.23(a), printed pp.1114,1117.
The corrected 15.2.21(1),(3) producer remains qt-e-152-char2-small-actions.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The actual S₃-square quotient already supplies a proper S-invariant
subgroup of K/O₂(K), retaining the original S and K. -/
theorem reducible_of_symmetricThreePair
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H) := by
  let K := smallActionK H
  let S := smallActionS T ZS
  let J := KS H T ZS
  have hTH : (T : Subgroup G) ≤ H := by rw [←d.residual_sup_sylow]; exact le_sup_right
  have hn : S ≤ normalizer (K : Set G) :=
    (show S ≤ (T : Subgroup G) from inf_le_left).trans
      (hTH.trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))))
  have hr : (pResidual 2 J).map J.subtype = K :=
    embedded_pResidual_join_pGroup K S (isPPerfect_embedded_pResidual 2 H)
      (T.isPGroup'.to_le inf_le_left) hn
  obtain ⟨e⟩ := hpair
  obtain ⟨L,hLn,hQL,hLR⟩ := SymmetricThreeProductResidual.exists_normal_intermediate e
  let := hLn
  let D := L.map J.subtype
  have hk : IsPGroup 2 J.subtype.ker := by
    rw [(MonoidHom.ker_eq_bot_iff J.subtype).mpr J.subtype_injective]
    exact IsPGroup.of_bot
  have hcore : ((pResidual 2 J).pCoreIn 2).map J.subtype = K.pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup J.subtype hk,hr]
  have hQD : K.pCoreIn 2 ≤ D := hcore ▸ map_mono hQL.le
  have hDK : D ≤ K := hr ▸ map_mono hLR.le
  have hJD : J ≤ normalizer (D : Set G) := by
    have hh := L.le_normalizer_map J.subtype
    rw [L.normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  intro hi
  rcases hi.2 D hQD hDK (le_sup_right.trans hJD) with he | he
  · exact hQL.ne (map_injective J.subtype_injective (hcore.trans he.symm))
  · exact hLR.ne (map_injective J.subtype_injective (he.trans hr.symm))

/-- The earlier Kc centralization clause identifies Kc with the literal KI.
This uses the residual of the full plane centralizer, not a family label. -/
theorem KI_eq_Kc_of_centralizes
    (hI : PlaneEscapes Mc ZS I)
    (hX : X = (primeToResidual 3 I).map I.subtype)
    (hc : smallActionKc H Mc ≤ centralizer (ZS : Set G)) :
    KI X ZS = smallActionKc H Mc := by
  rw [KI_eq_global_centralizer_residual d hI hX]
  have hi := embedded_primeToResidual_intersection 3 Mc (centralizer (ZS : Set G))
  rw [←d.orbit_residual,inf_eq_left.mpr hc,←d.centralizer_eq] at hi
  have hid := congrArg (Subgroup.map Mc.subtype)
    (embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 Mc) le_rfl)
  rw [map_embedded_primeToResidual_of_hom,←d.orbit_residual] at hid
  exact hi.symm.trans hid

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
