module
public import Stellmacher.SectionEight.EightSixSelectedOrbitCore

/-!
# The selected coatom centralizes the center orbit modulo the next line

In the central first-step branch of (8.6), let E lie in the next stabilizer
and A0 lie in the initial two-core. If [E,A0] lies in the next two-core,
then A0 centralizes the E-orbit closure of the initial center modulo the
next center. The actual actor coatom from (7.8) satisfies these premises.
No large-index assumption, orbit-core containment or classification model
is needed for this commutator calculation.

The supplied commutator condition puts A0 in the stabilizer of every
E-conjugate of the initial vertex. Each corresponding center has order
four and contains the fixed order-two next center. The common normalizer
acts trivially on that index-two quotient. Closure induction combines
these bounds into the commutator bound for the whole selected orbit.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), printed p.43,
assertion (11), the implication from (iv); refs/files/stellmacher-n-group.pdf.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement
universe u

private theorem commutator_closure_le
    {G : Type u} [Group G] (P Z A : Subgroup G) (X : Set G)
    (hXP : X ⊆ P) (hN : P ≤ Subgroup.normalizer (Z : Set G))
    (hX : ∀ x ∈ X, ∀ a ∈ A, ⁅x,a⁆ ∈ Z) : ⁅Subgroup.closure X,A⁆ ≤ Z := by
  apply Subgroup.commutator_le.mpr
  intro x hx a ha
  have hh : x ∈ P ∧ ∀ a ∈ A, ⁅x,a⁆ ∈ Z := by
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact ⟨hXP hx,hX x hx⟩
    | one => exact ⟨P.one_mem,by simp⟩
    | mul x y hx hy hix hiy =>
      refine ⟨P.mul_mem hix.1 hiy.1, ?_⟩
      intro a ha
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact Z.mul_mem (Subgroup.le_normalizer_iff.mp hN x hix.1 _ (hiy.2 a ha))
        (hix.2 a ha)
    | inv x hx hix =>
      refine ⟨P.inv_mem hix.1, ?_⟩
      intro a ha
      rw [commutatorElement_inv_left, ← commutatorElement_inv]
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
        (hN (P.inv_mem hix.1)) _).mp (Z.inv_mem (hix.2 a ha))
  exact hh.2 a ha

public theorem eight_six_selected_orbit_commutator_le
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (E A0 : Subgroup G)
    (hE : E ≤ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hA0 : A0 ≤ QAt ctx.Γ ctx.criticalPath.a)
    (hcomm : ⁅E, A0⁆ ≤ QAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E,A0⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hfirst : cp.firstStep ∈ Neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hback : cp.a ∈ Neighborhood Γ cp.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  have hQself : QAt Γ cp.a ≤ GAt Γ cp.a := by
    change Γ.twoCoreAt cp.a ≤ Γ.vertexStabilizer cp.a
    rw [Γ.twoCoreAt_def]; exact Subgroup.map_subtype_le _
  have hQaNext : QAt Γ cp.a ≤ GAt Γ cp.firstStep :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a cp.firstStep hfirst default).2.2
  have hZaQa : ZAt Γ cp.a ≤ QAt Γ cp.a :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep hfirst).trans
      (Subgroup.map_subtype_le _)
  have hZaP := hZaQa.trans hQaNext
  have hnext_le_initial : QAt Γ cp.firstStep ≤ GAt Γ cp.a :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.firstStep cp.a hback default).2.2
  have hA0initial := hA0.trans hQself
  obtain ⟨hlineCard,hline⟩ := eight_six_first_step_fixed_line_local ctx hcenter hcard
  have hlineN : GAt Γ cp.firstStep ≤
      Subgroup.normalizer (ZAt Γ cp.firstStep : Set G) := stabilizer_le_normalizer_z Γ _
  have hconj (g : G) (hg : g ∈ E) :
      ⁅conjugateBy (ZAt Γ cp.a) g,A0⁆ ≤ ZAt Γ cp.firstStep := by
    let vertex := Γ.act g⁻¹ cp.a
    have hge : g ∈ GAt Γ cp.firstStep := hE hg
    have hconjZ : ZAt Γ vertex = conjugateBy (ZAt Γ cp.a) g := by
      change z Γ (Γ.act g⁻¹ cp.a) = _
      rw [z_act, inv_inv]
      rfl
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
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hlineV).toEquiv,
        hlineCard,hcardV] at heq
      change (ZAt Γ cp.firstStep).relIndex (ZAt Γ vertex) * 2 = 4 at heq
      omega
    rw [← hconjZ]
    exact commutator_le_of_normalizing_index_two _ _ _ hindex
      (hA0vertex.trans (stabilizer_le_normalizer_z Γ vertex))
      ((hA0.trans hQaNext).trans hlineN)
  refine commutator_closure_le (GAt Γ cp.firstStep) _ A0 _ ?_ hlineN ?_
  · rintro x ⟨g,z,rfl⟩
    exact (GAt Γ cp.firstStep).mul_mem
      ((GAt Γ cp.firstStep).mul_mem (hE g.property) (hZaP z.property))
      ((GAt Γ cp.firstStep).inv_mem (hE g.property))
  · rintro x ⟨g,z,rfl⟩ a ha
    exact Subgroup.commutator_le.mp (hconj g g.property)
      _ (Subgroup.mem_map.mpr ⟨z,z.property,rfl⟩) a ha

end Stellmacher.SectionEight
