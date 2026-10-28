module

public import CFSG.Quasithin.Chapter12.Section06.Setup
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import Theory.GroupTheory.PGroup.SubnormalCore
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.SpecificGroups.AlternatingEight.ReducedCover

/-!
# The original Section06 action kernel and two-central core

The chosen Irr⁺ member makes O₂(L) centralize V. The given A₈ action quotient
therefore factors through L/O₂(L), which is quasisimple by Hypothesis 12.2.3.
Schur's universal double cover shows that the factored epimorphism has
trivial kernel, since L/O₂(L) has trivial two-core. Thus C_L(V)=O₂(L).
The same marked equivalence makes L/O₂(L) centerless, giving O₂,Z(L)=O₂(L).

These are consequences of the literal SourceHypothesis, with no additional
cover, kernel, simplicity or centralizer premise. The induced A₈ equivalence
commutes with the original projection and intertwines the same action on
V/C_V(L). They supply the opening kernel identification used by the A₆
point-stabilizer calculation; they do not prove Theorem 12.6.2 or C_V(L)=1.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Section 12.6,
printed p.822, using I.1.3(1) and the existing GLS III, Theorem 5.2.3 proof.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
universe u
variable {G : Type u} [Group G] [Finite G]

theorem OrthogonalMarking.actionKernel_eq_core
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (hq : IsQuasisimple (Star L)) :
    (conjugation L V chosen.normalizes).ker = pCore 2 L := by
  let J := LT T L
  let : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer chosen.sylow_normalizes_component)
  have hc : L.pCoreIn 2 ≤ J.pCoreIn 2 :=
    pCoreAmbient_mono_of_isSubnormalIn L J 2 le_sup_left
      (show (L.subgroupOf J).Normal from inferInstance).isSubnormal
  have hk : pCore 2 L ≤ (conjugation L V chosen.normalizes).ker := by
    rw [conjugation_ker]
    intro l hl
    exact chosen.core_centralizes (hc (mem_map_of_mem L.subtype hl))
  let f₀ : L →* alternatingGroup (Fin 8) := D.groupEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (conjugation L V chosen.normalizes).ker)
  have hf₀ : Function.Surjective f₀ :=
    D.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkill : pCore 2 L ≤ f₀.ker := by
    intro l hl
    change D.groupEquiv (QuotientGroup.mk' (conjugation L V chosen.normalizes).ker l) = 1
    have h : QuotientGroup.mk' (conjugation L V chosen.normalizes).ker l = 1 :=
      (QuotientGroup.eq_one_iff l).mpr (hk hl)
    rw [h, map_one]
  let f : Star L →* alternatingGroup (Fin 8) := QuotientGroup.lift (pCore 2 L) f₀ hkill
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨l, rfl⟩ := hf₀ a
    exact ⟨QuotientGroup.mk' (pCore 2 L) l, rfl⟩
  let := hq
  have hinj : Function.Injective f :=
    AlternatingEight.reduced_cover_injective f hf (pCore_quotient_pCore_eq_bot 2)
  apply le_antisymm _ hk
  intro l hl
  have hzero : f (QuotientGroup.mk' (pCore 2 L) l) = 1 := by
    change D.groupEquiv (QuotientGroup.mk' (conjugation L V chosen.normalizes).ker l) = 1
    have h : QuotientGroup.mk' (conjugation L V chosen.normalizes).ker l = 1 :=
      (QuotientGroup.eq_one_iff l).mpr hl
    rw [h, map_one]
  exact (QuotientGroup.eq_one_iff l).mp (hinj (hzero.trans f.map_one.symm))

theorem SourceHypothesis.actionKernel_eq_core
    {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}
    (H : SourceHypothesis K T L V) :
    (conjugation L V H.chosen.normalizes).ker = pCore 2 L := by
  let := H.chosen.elementary
  obtain ⟨D⟩ := H.orthogonal
  exact D.actionKernel_eq_core H.chosen H.source.quasisimple

theorem SourceHypothesis.centralizer_eq_core
    {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}
    (H : SourceHypothesis K T L V) :
    L ⊓ centralizer (V : Set G) = L.pCoreIn 2 := by
  have he := H.actionKernel_eq_core
  rw [conjugation_ker] at he
  have hm := congrArg (Subgroup.map L.subtype) he
  simpa only [subgroupOf_map_subtype, inf_comm, pCoreIn] using hm
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Reindex the given A₈ marking by the actual two-core quotient. -/
noncomputable def OrthogonalMarking.coreQuotientEquiv
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (hq : IsQuasisimple (Star L)) : Star L ≃* alternatingGroup (Fin 8) :=
  (QuotientGroup.quotientMulEquivOfEq (D.actionKernel_eq_core chosen hq).symm).trans D.groupEquiv

theorem OrthogonalMarking.coreQuotientEquiv_mk
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (hq : IsQuasisimple (Star L)) (l : L) :
    D.coreQuotientEquiv chosen hq (QuotientGroup.mk' (pCore 2 L) l) =
      D.groupEquiv (QuotientGroup.mk' (conjugation L V chosen.normalizes).ker l) := by
  exact congrArg D.groupEquiv
    (QuotientGroup.quotientMulEquivOfEq_mk (D.actionKernel_eq_core chosen hq).symm l)

theorem OrthogonalMarking.coreQuotient_center_eq_bot
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (hq : IsQuasisimple (Star L)) : center (Star L) = ⊥ := by
  let e := D.coreQuotientEquiv chosen hq
  apply bot_unique
  intro x hx
  have hc : e x ∈ center (alternatingGroup (Fin 8)) := by
    rw [mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (hx z)
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hc
  exact mem_bot.mpr (e.injective (hc.trans e.map_one.symm))

/-- O₂,Z(L)=O₂(L) under the original Section06 hypotheses. -/
theorem SourceHypothesis.twoCentralCore_eq_core
    {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}
    (H : SourceHypothesis K T L V) : twoCentralCore L = pCore 2 L := by
  let := H.chosen.elementary
  obtain ⟨D⟩ := H.orthogonal
  unfold twoCentralCore
  rw [D.coreQuotient_center_eq_bot H.chosen H.source.quasisimple,
    MonoidHom.comap_bot, QuotientGroup.ker_mk']
end CFSG.Quasithin.Chapter12.Section06
