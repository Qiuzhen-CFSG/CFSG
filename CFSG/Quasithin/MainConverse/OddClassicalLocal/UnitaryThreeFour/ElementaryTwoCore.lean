module

public import CFSG.Quasithin.MainConverse.OddClassicalLocal.UnitaryThreeFour.DimensionFour
public import Theory.GroupTheory.SylowLocalCentralizerCriterion
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.StandardInvolution

/-!
# PSU₄(3): reduction of elementary normalizers to involution centralizers

For a nontrivial normal elementary subgroup R of a Sylow two-subgroup T,
the ambient normalizer N of its image contains T. Its two-core is nontrivial,
and meets the center of T in an involution z. The existing Sylow-centralizer
criterion passes characteristic two from C_G(z) to N, using the intrinsic
cores and normality relative to each subgroup.

The final conditional assembly separates actual isomorphisms of involution
centralizers from the core calculation at diag(-1,-1,1,1). The latter's
projective centralizer includes matrices interchanging its eigenspaces.
Neither model premise is discharged here, so this module does not yet prove
the unconditional PSU₄(3) even-characteristic clause.

Source: Aschbacher–Smith, Theorem 0.1.2(4), with condition E on printed
pp.3–4 of `refs/quasithin.pdf` (repeated on pp.481–482).
-/

public section
namespace CFSG.Quasithin.MainConverse.UnitaryFourThree

open Subgroup Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal

/-- Relative normality puts T in the ambient normalizer. The Sylow-centralizer
criterion then controls its intrinsic core; maximality is unnecessary here. -/
theorem normal_elementary_core_of_involution_centralizers
    (T : Sylow 2 (Carrier 4))
    (hc : ∀ z : Carrier 4, orderOf z = 2 →
      Subgroup.centralizer (pCore 2 (Subgroup.centralizer ({z} : Set (Carrier 4))) :
        Set (Subgroup.centralizer ({z} : Set (Carrier 4)))) ≤
          pCore 2 (Subgroup.centralizer ({z} : Set (Carrier 4))))
    (R : Subgroup T) (hR : R ≠ ⊥) (hn : R.Normal) (he : IsElementaryAbelian 2 R) :
    let N := Subgroup.normalizer (R.map (T : Subgroup (Carrier 4)).subtype : Set (Carrier 4))
    Subgroup.centralizer (pCore 2 N : Set N) ≤ pCore 2 N := by
  let := hn
  let := he
  refine Subgroup.normalizer_core_selfCentralizing_of_sylow_centralizers T _
    ((IsElementaryAbelian.isPGroup 2 R).map _) ?_ ?_ ?_
  · intro hb
    apply hR
    apply (Subgroup.eq_bot_iff_forall R).mpr
    intro x hx
    apply Subtype.ext
    exact Subgroup.mem_bot.mp (hb ▸ Subgroup.mem_map_of_mem _ hx)
  · simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using
      R.le_normalizer_map (T : Subgroup (Carrier 4)).subtype
  · intro z _ hz
    exact hc z ((orderOf_coe z).trans hz)

/-- Two independent model calculations suffice: actual centralizer equivalences
and the intrinsic core calculation for the concrete representative. -/
theorem normal_elementary_core_of_centralizer_models
    (hmodels : ∀ z : Carrier 4, orderOf z = 2 →
      Nonempty (Subgroup.centralizer ({z} : Set (Carrier 4)) ≃* standardCentralizer))
    (hstandard : Subgroup.centralizer (pCore 2 standardCentralizer : Set standardCentralizer) ≤
      pCore 2 standardCentralizer)
    (T : Sylow 2 (Carrier 4)) (R : Subgroup T) (hR : R ≠ ⊥)
    (hn : R.Normal) (he : IsElementaryAbelian 2 R) :
    let N := Subgroup.normalizer (R.map (T : Subgroup (Carrier 4)).subtype : Set (Carrier 4))
    Subgroup.centralizer (pCore 2 N : Set N) ≤ pCore 2 N := by
  apply normal_elementary_core_of_involution_centralizers T ?_ R hR hn he
  intro z hz
  obtain ⟨e⟩ := hmodels z hz
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr hstandard

/-- Conditional assembly through the normal elementary subgroup reduction.
Both model premises must be discharged before this proves the source E clause. -/
theorem model_evenCharacteristic_of_centralizer_models
    (hmodels : ∀ z : Carrier 4, orderOf z = 2 →
      Nonempty (Subgroup.centralizer ({z} : Set (Carrier 4)) ≃* standardCentralizer))
    (hstandard : Subgroup.centralizer (pCore 2 standardCentralizer : Set standardCentralizer) ≤
      pCore 2 standardCentralizer) : IsEvenCharacteristic (Carrier 4) := by
  intro T
  apply model_evenCharacteristicAt_of_normal_elementary_cores
  intro R hR hn he N _
  exact normal_elementary_core_of_centralizer_models hmodels hstandard T R hR hn he

end CFSG.Quasithin.MainConverse.UnitaryFourThree
