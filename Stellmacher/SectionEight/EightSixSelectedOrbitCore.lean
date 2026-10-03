module
public import Stellmacher.SectionEight.GeneratedEightSixSubgroupForcingHelper
public import Stellmacher.SectionEight.GeneratedEightSixResidualCommutator
public import Stellmacher.SectionEight.GeneratedEightSixFirstCommutator
public import Stellmacher.SectionEight.GeneratedEightSixNormalizerExtraction
public import Stellmacher.SectionEight.EightFourSourceNineCommutingCore

/-!
# The selected center orbit lies in the initial core

In the distance-two configuration of Stellmacher (8.6), let A be the
predecessor neighbor core part, with |A : A intersect D| at least four.
Suppose the selected local group E lies in the next stabilizer and its
index-two actor subgroup A0 satisfies [E,A0] ≤ Qnext. Then the E-conjugates
of the initial center generate a subgroup inside the initial two-core.

The commutator condition puts A0 in the stabilizer of every conjugate
initial vertex. The conjugate center has order four and contains the
fixed order-two next center, so its commutator with A0 lies in that line.
If a conjugate center escaped the initial core, the cubic subgroup-forcing
lemma (4) would give A0 ≤ D, contradicting the prescribed large index.
Thus every conjugate generator lies in the initial core. The actual E and
A0 supplied by the geometric (7.8) extraction satisfy these premises;
no classification model or orbit-containment conclusion is assumed.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), printed p.43,
assertion (9); refs/files/stellmacher-n-group.pdf.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement
universe u

public theorem eight_six_selected_orbit_closure_le_initial_core
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hnormal : NormalIn D (GAt ctx.Γ ctx.criticalPath.a))
    (E A0 : Subgroup G)
    (hE : E ≤ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hA0 : A0 ≤ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hcoatom : Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a :
      Subgroup G) = 2 * Nat.card A0)
    (hcomm : ⁅E, A0⁆ ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G)) :
    conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlen : cp.length = 2 := hlength
  have hfirst : cp.firstStep ∈ Neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hback : cp.a ∈ Neighborhood Γ cp.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  have hnext_le_initial : QAt Γ cp.firstStep ≤ GAt Γ cp.a :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.firstStep cp.a hback default).2.2
  have hA0initial : A0 ≤ GAt Γ cp.a := (hA0.trans inf_le_right).trans
    (by change Γ.twoCoreAt cp.a ≤ Γ.vertexStabilizer cp.a
        rw [Γ.twoCoreAt_def]; exact Subgroup.map_subtype_le _)
  obtain ⟨hlineCard,hline⟩ := eight_six_first_step_fixed_line_local ctx hcenter hcard
  have hlineN : GAt Γ cp.firstStep ≤
      Subgroup.normalizer (ZAt Γ cp.firstStep : Set G) := stabilizer_le_normalizer_z Γ _
  have hZaQ : ZAt Γ cp.a ≤ QAt Γ cp.firstStep := by
    apply SevenSix.critical_minimality Γ cp
    rw [(SevenSix.adjacent_iff_distance_eq_one Γ).mp cp.firstStep_adj]
    omega
  have hconj_le (g : G) (hg : g ∈ E) :
      conjugateBy (ZAt Γ cp.a) g ≤ QAt Γ cp.a := by
    let vertex := Γ.act g⁻¹ cp.a
    have hge : g ∈ GAt Γ cp.firstStep := hE hg
    have hconjZ : ZAt Γ vertex = conjugateBy (ZAt Γ cp.a) g := by
      change z Γ (Γ.act g⁻¹ cp.a) = _
      rw [z_act, inv_inv]
      rfl
    have hconjQ : QAt Γ cp.firstStep =
        (QAt Γ cp.firstStep).map (MulAut.conj g).toMonoidHom :=
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (SevenSix.stabilizer_le_normalizer_q Γ cp.firstStep hge)).symm
    have hZnext : ZAt Γ vertex ≤ QAt Γ cp.firstStep := by
      rw [hconjZ, hconjQ]
      exact Subgroup.map_mono hZaQ
    have hlineEq : (ZAt Γ cp.firstStep).map (MulAut.conj g).toMonoidHom =
        ZAt Γ cp.firstStep :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hlineN hge)
    have hlineV : ZAt Γ cp.firstStep ≤ ZAt Γ vertex := by
      rw [hconjZ, ← hlineEq]
      exact Subgroup.map_mono hline
    have hcardV : Nat.card (ZAt Γ vertex) = 4 := by
      rw [hconjZ, conjugateBy, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hcard
    have hA0vertex : A0 ≤ GAt Γ vertex := by
      intro a ha
      have hc : ⁅g⁻¹,a⁆ ∈ QAt Γ cp.firstStep :=
        hcomm (Subgroup.commutator_mem_commutator (E.inv_mem hg) ha)
      have hga : g⁻¹ * a * g ∈ GAt Γ cp.a := by
        have hm := (GAt Γ cp.a).mul_mem (hnext_le_initial hc) (hA0initial ha)
        simpa [commutatorElement_def, mul_assoc] using hm
      change a ∈ stabilizer Γ (Γ.act g⁻¹ cp.a)
      rw [stabilizer_act, inv_inv]
      exact Subgroup.mem_map.mpr ⟨g⁻¹ * a * g, hga, by simp [mul_assoc]⟩
    have hindex : (ZAt Γ cp.firstStep).relIndex (ZAt Γ vertex) = 2 := by
      have heq := ((ZAt Γ cp.firstStep).subgroupOf (ZAt Γ vertex)).index_mul_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hlineV).toEquiv] at heq
      rw [hlineCard,hcardV] at heq
      change (ZAt Γ cp.firstStep).relIndex (ZAt Γ vertex) * 2 = 4 at heq
      omega
    have hA0next : A0 ≤ GAt Γ cp.firstStep := by
      exact (hA0.trans inf_le_right).trans
        ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a cp.firstStep hfirst default).2.2
    have hbracket : ⁅ZAt Γ vertex,A0⁆ ≤ ZAt Γ cp.firstStep :=
      commutator_le_of_normalizing_index_two _ _ _ hindex
        (hA0vertex.trans (stabilizer_le_normalizer_z Γ vertex))
        (hA0next.trans hlineN)
    by_contra hnot
    obtain ⟨x,hx,houtside⟩ := SetLike.not_le_iff_exists.mp hnot
    have hxV : x ∈ ZAt Γ vertex := hconjZ.ge hx
    have hforced : A0 ≤ D := by
      apply eight_six_cubic_subgroup_forcing ctx.sectionSeven Γ cp.a cp.firstStep previous
        hquot hfirst hprev.1 hprev.2 D hD hnormal x (hZnext hxV) houtside A0
      · exact (hA0.trans inf_le_left).trans
          (eight_six_neighborhood_closure_le_core Γ cp (by omega) previous)
      · exact (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hxV)).trans
          ((Subgroup.commutator_comm (ZAt Γ vertex) A0 ▸ hbracket).trans (hline.trans
            (eight_six_initial_center_le_intersection_of_length_two Γ cp hlen
              previous hprev.1 D hD)))
    have hbound : Nat.card A0 ≤ Nat.card
        ((VAt Γ previous ⊓ QAt Γ cp.a) ⊓ D : Subgroup G) :=
      Subgroup.card_le_of_le (le_inf hA0 hforced)
    have hpos : 0 < Nat.card A0 := Nat.card_pos
    change Nat.card A0 ≤ Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) at hbound
    omega
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨g,z,rfl⟩
  exact hconj_le g g.property (Subgroup.mem_map.mpr ⟨z,z.property,rfl⟩)

end Stellmacher.SectionEight
