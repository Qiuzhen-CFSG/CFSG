module
public import Stellmacher.SectionEight.EightSixCostFourInitialPairCard
public import Stellmacher.SectionEight.EightSixCommonStructure

/-!
# The cost-four core modulo the initial center is elementary abelian

Retain the actual selected cost-four configuration, its prescribed core Q,
and its initial center Za. Then Q/Za is elementary abelian. No special-group
identification or initial residual-core equality is assumed. This is the
central-quotient input to the native four-module construction in (8.6)(b).

The two neighboring V/core intersections A and B meet in Za. The initial
core normalizes each, so their mutual commutator lies in Za. The existing
neighbor-join bounds place the commutators and squares within each factor
in Za. The common structural theorem gives D elementary and [D,L]=Za.
Using Q=A B D, commutator generation first puts [Q,Q] in Za; the square map
on this abelian quotient then kills each generating factor. Thus every
square also lies in Za, the Frattini subgroup lies in Za, and the literal
quotient witness is elementary abelian.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6)(b1), printed p.44,
the initial special-core geometry. The proof isolates its central-quotient
conclusion for the independently constructed native module.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_cost_four_central_quotient
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
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4) :
    QuotientIsElementaryAbelian Q (ZAt ctx.Γ ctx.criticalPath.a) 2 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let B := VAt Γ cp.firstStep ⊓ QAt Γ cp.a
  let Z := ZAt Γ cp.a
  have hpair := eight_six_cost_four_initial_pair_card ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  have hAB : A ⊓ B = Z := hpair.2.2.2.1
  have hbase := eight_six_common_structure_local ctx hcenter hquot hlength hcard
    previous hprev D L Q hD hL hQ
  have hDL : ⁅D,L⁆ = Z := hbase.2.1
  let _ : IsElementaryAbelian 2 D := hbase.2.2.2
  have hgen : Q = A ⊔ B ⊔ D := data.core_generation
  have hAQ : A ≤ Q := hgen ▸ le_sup_left.trans le_sup_left
  have hBQ : B ≤ Q := hgen ▸ le_sup_right.trans le_sup_left
  have hDQ : D ≤ Q := hgen ▸ le_sup_right
  have hQL : Q ≤ L := hQ ▸ twoCoreIn_le L
  have hQP : Q ≤ GAt Γ cp.a := hQL.trans data.closure_le
  have hnormal : GAt Γ cp.a ≤ Subgroup.normalizer (Z : Set G) :=
    stabilizer_le_normalizer_z Γ cp.a
  have hQnormal : Q ≤ Subgroup.normalizer (Z : Set G) := hQP.trans hnormal
  have hfirst : cp.firstStep ∈ Neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hAaction := eight_six_generation_neighbor_action ctx.sectionSeven Γ cp
    (by change 1 < ctx.criticalPath.length; omega) previous hprev.1
  have hBaction := eight_six_generation_neighbor_action ctx.sectionSeven Γ cp
    (by change 1 < ctx.criticalPath.length; omega) cp.firstStep hfirst
  have hABcomm : ⁅A,B⁆ ≤ Z := by
    rw [←hAB]
    refine le_inf ?_ ?_
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (inf_le_right.trans hAaction.1)
    · rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (inf_le_right.trans hBaction.1)
  have hAbounds := eight_six_neighbor_join_bounds_local ctx hcenter hlength hcard
    Z hnormal le_rfl data.first_commutator previous hprev.1
  have hBbounds := eight_six_neighbor_join_bounds_local ctx hcenter hlength hcard
    Z hnormal le_rfl data.first_commutator cp.firstStep hfirst
  have hAA : ⁅A,A⁆ ≤ Z :=
    (Subgroup.commutator_mono inf_le_left inf_le_left).trans hAbounds.1
  have hBB : ⁅B,B⁆ ≤ Z :=
    (Subgroup.commutator_mono inf_le_left inf_le_left).trans hBbounds.1
  have hDcomm : ⁅D,Q⁆ ≤ Z :=
    (Subgroup.commutator_mono le_rfl hQL).trans hDL.le
  have hfamily : Q = sSup {A,B,D} := by
    simpa only [sSup_insert,sSup_singleton,sup_assoc] using hgen
  have hcontain : ∀ H ∈ ({A,B,D} : Set (Subgroup G)), H ≤ Q := by
    intro H hH
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hH
    rcases hH with rfl | rfl | rfl
    · exact hAQ
    · exact hBQ
    · exact hDQ
  have hcomm : ∀ H ∈ ({A,B,D} : Set (Subgroup G)),
      ∀ K ∈ ({A,B,D} : Set (Subgroup G)), ⁅H,K⁆ ≤ Z := by
    intro H hH K hK
    have hKQ := hcontain K hK
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hH hK
    rcases hH with rfl | rfl | rfl
    · rcases hK with rfl | rfl | rfl
      · exact hAA
      · exact hABcomm
      · rw [Subgroup.commutator_comm]
        exact (Subgroup.commutator_mono le_rfl hAQ).trans hDcomm
    · rcases hK with rfl | rfl | rfl
      · rwa [Subgroup.commutator_comm]
      · exact hBB
      · rw [Subgroup.commutator_comm]
        exact (Subgroup.commutator_mono le_rfl hBQ).trans hDcomm
    · exact (Subgroup.commutator_mono le_rfl hKQ).trans hDcomm
  have hderived : ⁅Q,Q⁆ ≤ Z := by
    rw [hfamily]
    apply eight_six_commutator_sSup_le _ _ _ Q hQnormal hcontain
    intro H hH
    rw [Subgroup.commutator_comm]
    exact eight_six_commutator_sSup_le _ _ _ Q hQnormal hcontain
      (fun K hK => hcomm K hK H hH)
  have hsquares : ∀ x ∈ Q, x^2 ∈ Z := by
    apply eight_six_squares_of_involution_join {A,B,D} Q Z hfamily hQnormal hderived
    intro H hH x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hH
    rcases hH with hH | hH | hH
    · subst H
      exact hAbounds.2 x hx.1
    · subst H
      exact hBbounds.2 x hx.1
    · subst H
      have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 D) (⟨x,hx⟩ : D)
      have heq : x^2 = 1 := congrArg Subtype.val hh
      rw [heq]
      exact Z.one_mem
  have htwo : IsPGroup 2 Q := hQ ▸ eight_six_two_core_is_two_group L
  exact eight_six_quotient_elementary_of_frattini_le Q Z htwo
    (Subgroup.normal_subgroupOf_of_le_normalizer hQnormal)
    (eight_six_frattini_le_of_commutators_and_squares Q Z htwo hderived hsquares)

end Stellmacher.SectionEight
