module
public import Stellmacher.SectionEight.EightSixHighCostActorRank

/-!
# The high-cost core action quotient has rank three

For the actual selected high-cost configuration of Stellmacher (8.6), the
quotient Q/(Q intersect Qnext) is elementary abelian of order eight. The
full selected local telescope and elementary D are retained; the graph
actor rank is obtained from its proved producer.

Use the native quotient of Q by its intersection with the next core. The
intersection is normal because Q lies in the next stabilizer. Equation-one
generation writes Q as the join of A, the next neighbor join intersected
with Qa, and D. The latter two subgroups are in Qnext, so the quotient is
the image of A. Its kernel is exactly A intersect D, and the proved actor
quotient has order eight. The common Frattini bound lies in D and hence
in the kernel, giving commutativity and exponent two in this same native
quotient. No faithful-action replacement or assumed rank is used.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6)(c), printed p.41,
and the graph actor calculation following (18), printed p.45. This is the
exact elementary rank-three core quotient in the public case-C alternative.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_high_cost_core_action_rank
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (helementary : IsElementaryAbelianSubgroup 2 D) :
    QuotientElementaryAbelian Q (Q ⊓ QAt ctx.Γ ctx.criticalPath.firstStep) 2 3 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let Qa := QAt Γ cp.a
  let A := VAt Γ previous ⊓ Qa
  let B := V ⊓ Qa
  let N := Q ⊓ R
  have hlen : cp.length = 2 := hlength
  have hgen : Q = A ⊔ B ⊔ D := data.core_generation
  have hAQ : A ≤ Q := hgen ▸ le_sup_of_le_left le_sup_left
  have hBQ : B ≤ Q := hgen ▸ le_sup_of_le_left le_sup_right
  have hDQ : D ≤ Q := hgen ▸ le_sup_right
  have hDR : D ≤ R := hD ▸ inf_le_right
  have hBR : B ≤ R := inf_le_left.trans
    (neighbor_join_le_core_of_length_gt_one Γ cp (by omega) cp.firstStep)
  have hDN : D ≤ N := le_inf hDQ hDR
  have hcores := eight_six_rigidity_core_containments ctx.sectionSeven Γ cp previous D L Q hD data
  have hfirst : cp.firstStep ∈ Neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hQP : Q ≤ GAt Γ cp.firstStep := hcores.2.1.trans
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a cp.firstStep hfirst default).2.2)
  have hQN : Q ≤ Subgroup.normalizer (N : Set G) :=
    (le_inf Q.le_normalizer (hQP.trans (stabilizer_le_normalizer_q Γ cp.firstStep))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  let hN : (N.subgroupOf Q).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQN
  let _ := hN
  let W := Q ⧸ N.subgroupOf Q
  let π : Q →* W := QuotientGroup.mk' (N.subgroupOf Q)
  have hBker : B.subgroupOf Q ≤ π.ker := by
    intro b hb
    exact (QuotientGroup.eq_one_iff _).mpr ⟨b.property,hBR hb⟩
  have hDker : D.subgroupOf Q ≤ π.ker := by
    intro d hd
    exact (QuotientGroup.eq_one_iff _).mpr (hDN hd)
  have hnativeGen : A.subgroupOf Q ⊔ B.subgroupOf Q ⊔ D.subgroupOf Q = ⊤ := by
    rw [←Subgroup.subgroupOf_sup hAQ hBQ,
      ←Subgroup.subgroupOf_sup (sup_le hAQ hBQ) hDQ,←hgen,Subgroup.subgroupOf_self]
  have hAimage : (A.subgroupOf Q).map π = ⊤ := by
    have hh := congrArg (Subgroup.map π) hnativeGen
    rw [Subgroup.map_sup,Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff _).mpr hBker,(Subgroup.map_eq_bot_iff _).mpr hDker,
      sup_bot_eq,sup_bot_eq,Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  have hkernel : A.subgroupOf Q ⊓ π.ker = (A ⊓ D).subgroupOf Q := by
    ext a
    constructor
    · intro h
      have haR : (a:G) ∈ R := ((QuotientGroup.eq_one_iff _).mp h.2).2
      exact ⟨h.1,hD ▸ ⟨(neighbor_join_le_core_of_length_gt_one Γ cp (by omega) previous) h.1.1,haR⟩⟩
    · intro h
      exact ⟨h.1,(QuotientGroup.eq_one_iff _).mpr (hDN h.2)⟩
  have harank := eight_six_high_cost_actor_rank ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hhigh helementary
  have hindex : (A ⊓ D).relIndex A = 8 := by
    have hh := ((A ⊓ D).subgroupOf A).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show A ⊓ D ≤ A from inf_le_left)).toEquiv] at hh
    change (A ⊓ D).relIndex A * Nat.card (A ⊓ D : Subgroup G) = Nat.card A at hh
    change Nat.card A = 8 * Nat.card (A ⊓ D : Subgroup G) at harank
    have hp : 0 < Nat.card (A ⊓ D : Subgroup G) := Nat.card_pos
    nlinarith
  have hAcard : Nat.card ((A.subgroupOf Q).map π) = 8 := by
    rw [←Subgroup.relIndex_ker,←Subgroup.inf_relIndex_left (A.subgroupOf Q) π.ker,
      hkernel,Subgroup.relIndex_subgroupOf hAQ]
    exact hindex
  have hWcard : Nat.card W = 8 := by simpa only [hAimage,Subgroup.card_top] using hAcard
  have hQtwo : IsPGroup 2 Q := by
    rw [hQ,twoCoreIn]
    exact (pCore_isPGroup (p := 2)).map _
  let _ : Fact (IsPGroup 2 Q) := ⟨hQtwo⟩
  have hPhi : frattini Q ≤ N.subgroupOf Q := by
    intro q hq
    exact hDN (data.core_frattini_le (Subgroup.mem_map.mpr ⟨q,hq,rfl⟩))
  have hWel : IsElementaryAbelian 2 W := {
    toIsMulCommutative :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N.subgroupOf Q)).2
        ((commutator_le_frattini_of_isPGroup (p := 2)).trans hPhi)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun w => by
      refine QuotientGroup.induction_on w ?_
      intro q
      change (π q)^2=1
      rw [←map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hPhi (pth_power_mem_frattini_of_isPGroup (p := 2) q)) }
  let witness : QuotientWitness Q N := {
    X := W
    projection := π
    surjective := QuotientGroup.mk'_surjective _
    kernel_eq := QuotientGroup.ker_mk' _ }
  exact ⟨witness,hWel,hWcard⟩
end Stellmacher.SectionEight
