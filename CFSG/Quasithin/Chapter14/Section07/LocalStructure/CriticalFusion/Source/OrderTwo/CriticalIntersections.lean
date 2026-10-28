module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.ModuleTransport
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.Selection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.DualSection

/-!
# Source critical intersections for 14.7.69

The original-section calculations imply (b)–(e), equal critical ranks, and the
group-side hyperplane bound on the exact section Q_H/C_{Q_H}(U). This module
assembles the transported duality contradiction, reciprocal setup, (f), and the
exclusion of |U₀| = 2 under the explicit source hypotheses used by the final
critical-fusion assembly.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Lemma 14.7.69, printed pp.1072–1073.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

namespace CriticalIntersections

omit [Finite G] in
theorem critical_right_transport (c : CriticalPath (L := L) F) :
    c.Uα = conjugate F.U c.conjugator ∧
      c.Zα = conjugate (F.Vi 1) c.conjugator ∧
      c.Qα = (conjugate F.H c.conjugator).pCoreIn 2 :=
  ⟨rfl, rfl, rfl⟩

theorem point_not_le_Uα
    (d : Data T L V F W) (hc : d.SectionCentralizer)
    (hs : d.ModuleSeparation)
    (s : SourceDuality F X Y) (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hm : ModuleCalculations d c (c.Uα_le_H earlier))
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hfull : star F c.Uα = star F (Q T L))
    (h : F.H) (hhA : (h : G) ∈ c.Uα)
    (hr : Module.finrank (ZMod 2) (d.action h - LinearMap.id).range = 2)
    (hd : Disjoint (d.action h - LinearMap.id).range d.projection.toLinearMap.ker) :
    ¬ F.Vi 1 ≤ c.Uα := by
  intro hpoint
  have hlo := DualSection.critical_fixed_index_ge_four d hc s hcomm c earlier h hhA hr hd
  have hhi := dual_section_fixed_index_le_two_of_point_le d hc hs c earlier
    hUH hm hcomm hfull hpoint
  omega

structure ReciprocalCentralizer (c : CriticalPath (L := L) F) where
  conjugator : G
  centralizer_eq : c.Uα ⊓ centralizer (F.U : Set G) = conjugate V conjugator

structure ReciprocalSetup (d : Data T L V F W) (c : CriticalPath (L := L) F) where
  ranks : Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) =
      Nat.log 2 (Nat.card (star F c.Uα))
  right_conjugator : c.Uα = conjugate F.U c.conjugator
  right_point : c.Zα = conjugate (F.Vi 1) c.conjugator
  centralizer : ReciprocalCentralizer c

def reciprocal_setup
    (d : Data T L V F W) (hc : d.SectionCentralizer)
    (hs : d.ModuleSeparation) (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hm : ModuleCalculations d c (c.Uα_le_H earlier))
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hfull : star F c.Uα = star F (Q T L))
    (hrec : ReciprocalCentralizer c) :
    ReciprocalSetup d c := by
  have hr := equal_critical_ranks d hc hs c earlier hUH hm hcomm hfull
  exact
    { ranks := hr.1.trans hr.2.symm
      right_conjugator := (critical_right_transport c).1
      right_point := (critical_right_transport c).2.1
      centralizer := hrec }

theorem critical_intersection_inf_point_bot
    (c : CriticalPath (L := L) F) (hpoint : ¬ F.Vi 1 ≤ c.Uα) :
    (F.U ⊓ c.Uα) ⊓ (F.Vi 1) = ⊥ := by
  apply bot_unique
  intro x hx
  by_contra hne
  have hne' : (F.U ⊓ c.Uα) ⊓ (F.Vi 1) ≠ ⊥ := by
    intro heq
    apply hne
    exact heq ▸ hx
  have hgt : 1 < Nat.card ↥((F.U ⊓ c.Uα) ⊓ (F.Vi 1)) :=
    (one_lt_card_iff_ne_bot _).mpr hne'
  have hle := Nat.card_le_card_of_injective
    (Subgroup.inclusion (inf_le_right : (F.U ⊓ c.Uα) ⊓ (F.Vi 1) ≤ F.Vi 1))
    (Subgroup.inclusion_injective (inf_le_right : (F.U ⊓ c.Uα) ⊓ (F.Vi 1) ≤ F.Vi 1))
  have hV1 : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have heq : (F.U ⊓ c.Uα) ⊓ (F.Vi 1) = F.Vi 1 := by
    apply eq_of_le_of_card_ge inf_le_right
    omega
  exact hpoint (by rw [← heq]; exact inf_le_left.trans inf_le_right)

theorem critical_commutator_eq_intersection
    (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hm : ModuleCalculations d c (c.Uα_le_H earlier))
    (hpoint : ¬ F.Vi 1 ≤ c.Uα) :
    ⁅F.U, c.Uα⁆ = F.U ⊓ c.Uα := by
  let : IsMulCommutative F.U := d.abelian
  have hp := centralizer_and_products d c (c.Uα_le_H earlier) hUH hm
  have hsupC : ⁅F.U, c.Uα⁆ ⊔ F.Vi 1 = d.U₀ ⊔ V := hp.1
  have hsupE : (F.U ⊓ c.Uα) ⊔ F.Vi 1 = d.U₀ ⊔ V := hp.2.1
  have hbotE := critical_intersection_inf_point_bot c hpoint
  have hnormE : F.Vi 1 ≤ normalizer ((F.U ⊓ c.Uα : Subgroup G) : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    apply commutator_le.mpr
    intro x hx y hy
    have hxy := isMulCommutative_iff.mp d.abelian
      ⟨x, d.conjugationSection.kernel_le hx⟩ ⟨y, hy.1⟩
    have hxy' : x * y = y * x := congrArg Subtype.val hxy
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hxy']
    exact (F.U ⊓ c.Uα).one_mem
  have hnormC : F.Vi 1 ≤ normalizer ((⁅F.U, c.Uα⁆ : Subgroup G) : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    apply commutator_le.mpr
    intro x hx y hy
    have hyU := (commutator_sandwich d c (c.Uα_le_H earlier) hUH).1 hy
    have hxy := isMulCommutative_iff.mp d.abelian
      ⟨x, d.conjugationSection.kernel_le hx⟩ ⟨y, hyU.1⟩
    have hxy' : x * y = y * x := congrArg Subtype.val hxy
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hxy']
    exact ⁅F.U, c.Uα⁆.one_mem
  have hcardE := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (F.U ⊓ c.Uα) (F.Vi 1) hnormE
  have hcardC := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    ⁅F.U, c.Uα⁆ (F.Vi 1) hnormC
  rw [hbotE, Subgroup.card_bot, hsupE] at hcardE
  have hbotC : ⁅F.U, c.Uα⁆ ⊓ (F.Vi 1) = ⊥ := by
    apply bot_unique
    intro x hx
    by_contra hne
    have hne' : ⁅F.U, c.Uα⁆ ⊓ (F.Vi 1) ≠ ⊥ := by
      intro heq
      apply hne
      exact heq ▸ hx
    have hgt : 1 < Nat.card ↥(⁅F.U, c.Uα⁆ ⊓ (F.Vi 1)) :=
      (one_lt_card_iff_ne_bot _).mpr hne'
    have hle := Nat.card_le_card_of_injective
      (Subgroup.inclusion (inf_le_right : ⁅F.U, c.Uα⁆ ⊓ (F.Vi 1) ≤ F.Vi 1))
      (Subgroup.inclusion_injective (inf_le_right : ⁅F.U, c.Uα⁆ ⊓ (F.Vi 1) ≤ F.Vi 1))
    have hV1 : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    have heq : ⁅F.U, c.Uα⁆ ⊓ (F.Vi 1) = F.Vi 1 := by
      apply eq_of_le_of_card_ge inf_le_right
      omega
    exact hpoint (by
      rw [← heq]
      exact inf_le_left.trans ((commutator_sandwich d c (c.Uα_le_H earlier) hUH).1.trans inf_le_right))
  rw [hbotC, Subgroup.card_bot, hsupC] at hcardC
  have hV1 : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hcard : Nat.card ↥(⁅F.U, c.Uα⁆ : Subgroup G) =
      Nat.card ↥(F.U ⊓ c.Uα) := by
    have heq := hcardC.trans hcardE.symm
    have hpos : 0 < Nat.card (F.Vi 1) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos heq
  exact eq_of_le_of_card_ge (commutator_sandwich d c (c.Uα_le_H earlier) hUH |>.1)
    (by simp [hcard])

theorem critical_intersection_complement
    (d : Data T L V F W) (hc : d.SectionCentralizer)
    (c : CriticalPath (L := L) F) (earlier : c.EarlierImages)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hm : ModuleCalculations d c (c.Uα_le_H earlier))
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hpoint : ¬ F.Vi 1 ≤ c.Uα) :
    ⁅F.U, c.Uα⁆ = F.U ⊓ c.Uα ∧
      (F.U ⊓ c.Uα) ⊓ F.Vi 1 = ⊥ ∧
      (F.U ⊓ c.Uα) ⊔ F.Vi 1 = d.U₀ ⊔ V ∧
      d.U₀ ⊔ V = F.U ⊓ centralizer (c.Uα : Set G) ∧
      F.U ⊓ c.Qα = d.U₀ ⊔ V := by
  have hp := centralizer_and_products d c (c.Uα_le_H earlier) hUH hm
  have hq := core_intersection d hc c (c.Uα_le_H earlier) hUH hm hcomm
  exact ⟨critical_commutator_eq_intersection d c earlier hUH hm hpoint,
    critical_intersection_inf_point_bot c hpoint, hp.2.1, hp.2.2.symm, hq⟩

theorem point_normalizes_critical_intersection
    (d : Data T L V F W) (c : CriticalPath (L := L) F) :
    F.Vi 1 ≤ normalizer ((F.U ⊓ c.Uα : Subgroup G) : Set G) := by
  let : IsMulCommutative F.U := d.abelian
  apply le_normalizer_iff_commutator_le_right.mpr
  apply commutator_le.mpr
  intro x hx y hy
  have hxy := isMulCommutative_iff.mp d.abelian
    ⟨x, d.conjugationSection.kernel_le hx⟩ ⟨y, hy.1⟩
  have hxy' : x * y = y * x := congrArg Subtype.val hxy
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hxy']
  exact (F.U ⊓ c.Uα).one_mem

theorem exclude_card_U₀_two
    (d : Data T L V F W) (hc : d.SectionCentralizer)
    (c : CriticalPath (L := L) F) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hm : ModuleCalculations d c (c.Uα_le_H earlier))
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hpoint : ¬ F.Vi 1 ≤ c.Uα)
    (hrec : ReciprocalCentralizer c) :
    Nat.card d.U₀ ≠ 2 := by
  intro hcard
  obtain ⟨_, hbot, hsup, _, _⟩ :=
    critical_intersection_complement d hc c earlier hUH hm hcomm hpoint
  have hV1 : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hU0eq : d.U₀ = F.Vi 1 := by
    have heq : F.Vi 1 = d.U₀ := by
      apply eq_of_le_of_card_ge d.point_le_U₀
      omega
    exact heq.symm
  have hU0V : d.U₀ ⊔ V = V := by
    apply sup_eq_right.mpr
    rw [hU0eq]
    exact F.le_seed 1
  have hsupV : (F.U ⊓ c.Uα) ⊔ F.Vi 1 = V := hsup.trans hU0V
  have hFV : F.U ⊓ c.Uα ≤ V := by
    exact (le_sup_left : F.U ⊓ c.Uα ≤ (F.U ⊓ c.Uα) ⊔ F.Vi 1).trans_eq hsupV
  have hnorm := point_normalizes_critical_intersection d c
  have hmul := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (F.U ⊓ c.Uα) (F.Vi 1) hnorm
  rw [hbot, Subgroup.card_bot, hsupV] at hmul
  rw [hV1] at hmul
  have hV : Nat.card V = 8 := by
    rw [← F.last]
    simpa using F.card 3 (by decide)
  rw [hV] at hmul
  have hFcard : Nat.card ↥(F.U ⊓ c.Uα) = 4 := by omega
  have hFleB : F.U ⊓ c.Uα ≤ c.Uα ⊓ centralizer (F.U : Set G) := by
    refine le_inf inf_le_right ?_
    intro x hx y hy
    exact (congrArg Subtype.val (isMulCommutative_iff.mp d.abelian
      ⟨x, hx.1⟩ ⟨y, hy⟩)).symm
  have hAg : F.U ⊓ c.Uα ≤ conjugate V hrec.conjugator :=
    hrec.centralizer_eq ▸ hFleB
  have hVeq := d.lemma_14_7_67_two sep (F.U ⊓ c.Uα) hFV hFcard
    hrec.conjugator hAg
  have hB : c.Uα ⊓ centralizer (F.U : Set G) = V :=
    hrec.centralizer_eq.trans hVeq
  apply hpoint
  have hV1V : F.Vi 1 ≤ V := F.le_seed 1
  have hV1B : F.Vi 1 ≤ c.Uα ⊓ centralizer (F.U : Set G) := by
    rw [hB]
    exact hV1V
  exact hV1B.trans inf_le_left

end CriticalIntersections
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
end
