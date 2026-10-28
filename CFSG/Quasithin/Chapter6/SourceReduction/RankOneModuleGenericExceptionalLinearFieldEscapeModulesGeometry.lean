module

public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import CFSG.Quasithin.ChapterG.Section02.CentralClosureConsequences
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The point-centralizer specialization of G.2.2

For an involution fixed by the original Sylow group, condition (E) makes
its centralizer characteristic two. Thus a local G.2.1 setup extends to
the whole point centralizer. G.2.2 puts the resulting conjugate span in
the local two-core, with Frattini subgroup and commutator subgroup in
the point. If that span is nonabelian, its commutator with the original
plane is exactly the point: otherwise invariance of its centralizer
would make the entire span abelian.

These are the initial reductions of 5.1.23. The later cubic action and
constituent contradiction are not asserted here.

Source: Aschbacher--Smith, G.2.2 and 5.1.21,23, printed pp.332,644--645.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {H V L : Subgroup G} {z : G}

/-- Enlarge the local overgroup to the whole involution centralizer. -/
public theorem centralizer_hypothesis
    (d : (ChapterG.Section02.Setup.mk V (zpowers z) L T H).Hypothesis)
    (hE : IsEvenCharacteristicAt T) (hz : orderOf z = 2) :
    (ChapterG.Section02.Setup.mk V (zpowers z) L T (centralizer ({z} : Set G))).Hypothesis := by
  have hpoint : normalizer (zpowers z : Set G) = centralizer ({z} : Set G) := by
    have hn := normalizer_le_centralizer_of_card_two (zpowers z)
      (show Nat.card (zpowers z) = 2 by simpa only [Nat.card_zpowers] using hz)
    simpa only [zpowers_eq_closure, centralizer_closure] using
      le_antisymm hn (Subgroup.centralizer_le_normalizer _)
  have hTG : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    rw [← hpoint]
    exact d.T_normalizes_point
  have hHG : H ≤ centralizer ({z} : Set G) := by
    rw [← hpoint]
    exact d.H_le
  have hchar : generalizedFitting (centralizer ({z} : Set G)) =
      pCore 2 (centralizer ({z} : Set G)) := by
    apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    exact Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      hE (isTwoLocal_involution_centralizer hz) hTG)
  refine {
    elementary := d.elementary
    point_ne_bot := d.point_ne_bot
    point_le := d.point_le
    residual := d.residual
    V_le_T := d.V_le_T
    T_normalizes_point := d.T_normalizes_point
    T_normalizes_V := d.T_normalizes_V
    T_normalizes_L := d.T_normalizes_L
    sylow_LT := d.sylow_LT
    H_le := ?_
    local_le := d.local_le.trans hHG
    sylow_H := ⟨T.subtype hTG, ?_⟩
    characteristic_two := hchar
    local_normalizes_V := d.local_normalizes_V
    quotient_nonzero := d.quotient_nonzero
    irreducible := d.irreducible }
  · change centralizer ({z} : Set G) ≤ normalizer (zpowers z : Set G)
    rw [hpoint]
  · exact map_subgroupOf_eq_of_le hTG

/-- G.2.2 on the actual centralizer span, before assuming abelianness. -/
public theorem centralizer_span_reductions
    (d : (ChapterG.Section02.Setup.mk V (zpowers z) L T H).Hypothesis)
    (hE : IsEvenCharacteristicAt T) (hz : orderOf z = 2) :
    let U := conjugateSpanBy V (centralizer ({z} : Set G))
    U ≤ (centralizer ({z} : Set G)).pCoreIn 2 ∧
      U ≤ (T : Subgroup G) ∧
      (frattini U).map U.subtype ≤ zpowers z ∧
      ⁅U, U⁆ ≤ zpowers z := by
  have h := centralizer_hypothesis d hE hz
  exact ⟨h.U_le_core, h.U_normal_in_T.1, h.frattini_U_le_point,
    (commutator_mono le_rfl h.U_le_core).trans h.commutator_U_core_le_point⟩

/-- The exact nontrivial commutator used to enter G.2.3 in 5.1.23. -/
public theorem nonabelian_plane_commutator
    (d : (ChapterG.Section02.Setup.mk V (zpowers z) L T H).Hypothesis)
    (hE : IsEvenCharacteristicAt T) (hz : orderOf z = 2)
    (hnon : ¬ IsMulCommutative (conjugateSpanBy V (centralizer ({z} : Set G)))) :
    ⁅V, conjugateSpanBy V (centralizer ({z} : Set G))⁆ = zpowers z := by
  let U := conjugateSpanBy V (centralizer ({z} : Set G))
  have hle : ⁅V, U⁆ ≤ zpowers z :=
    (commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans (centralizer_span_reductions d hE hz).2.2.2
  have hne : ⁅V, U⁆ ≠ ⊥ := by
    intro he
    have hc : V ≤ centralizer (U : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp he
    have hUC : U ≤ centralizer (U : Set G) := conjugateSpanBy_le hc
      ((le_normalizer_conjugateSpanBy _ _).trans (normalizer_le_normalizer_centralizer U))
    exact hnon (le_centralizer_iff_isMulCommutative.mp hUC)
  apply eq_of_le_of_card_ge hle
  rw [(show Nat.card (zpowers z) = 2 by simpa only [Nat.card_zpowers] using hz)]
  exact (one_lt_card_iff_ne_bot _).mpr hne

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
