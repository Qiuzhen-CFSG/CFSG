module
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexCenterCounts
public import Stellmacher.SectionEight.EightSixSelectedOrbitCommutator
public import Stellmacher.SectionEight.EightSixSelectedFixedCoreIntersection
public import Stellmacher.SectionEight.EightSixNextQuotientModule
public import Theory.GroupTheory.Commutator.ElementaryQuotientIndexTwoQuadratic

/-!
# The selected orbit has trivial double actor commutator

Let V1 be the actual E-orbit closure of Za in the large-index configuration
of (8.6), and suppose the proved source-(9) containment V1 ≤ Qa is supplied.
Then [[V1,A],A] is trivial, where A is the predecessor core part and E/A0
is the actual prescribed-actor geometric selection.

Source (11) says A0 centralizes V1 modulo the next center. The quotient
V1/Znext is elementary as a subgroup quotient of Vnext/Znext, and A0 has
index two in A. The central-quotient quadratic lemma therefore puts the
double commutator in Znext. Independently Qa normalizes Qprev, so
[V1,A] ≤ Qprev; the transported predecessor commutator identity puts its
commutator with A in Zprev. The distinct neighboring center lines are
disjoint, giving the claimed zero commutator.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), printed p.43,
the paragraph between assertions (11) and (12). No cardinality or model
conclusion of (12) is assumed here; the selected objects remain unchanged.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem eight_six_initial_core_double_actor_commutator_le_previous
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (U : Subgroup G) (hU : U ≤ QAt ctx.Γ ctx.criticalPath.a) :
    ⁅⁅U,VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a⁆,
      VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a⁆ ≤ ZAt ctx.Γ previous := by
  let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
  have hQaPrev : QAt ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ previous :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core
      ctx.criticalPath.a previous hprev default).2.2
  have hUprev : U ≤ Subgroup.normalizer (QAt ctx.Γ previous : Set G) :=
    (hU.trans hQaPrev).trans (SevenSix.stabilizer_le_normalizer_q ctx.Γ previous)
  have hAprev : A ≤ QAt ctx.Γ previous := inf_le_left.trans
    (SevenSix.neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath (by omega) previous)
  have hcomm : ⁅U,A⁆ ≤ QAt ctx.Γ previous :=
    (Subgroup.commutator_mono le_rfl hAprev).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hUprev)
  exact (Subgroup.commutator_mono hcomm inf_le_left).trans_eq
    (eight_six_predecessor_commutator_and_center_bound ctx.sectionSeven ctx.Γ
      ctx.criticalPath hcenter hcard previous hprev D L Q data).1

public theorem eight_six_selected_orbit_double_commutator_eq_bot
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
      QAt ctx.Γ ctx.criticalPath.a) :
    ⁅⁅conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E,
      VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a⁆,
      VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a⁆ = ⊥ := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let U := conjugateClosure (ZAt Γ cp.a) E
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hA0A : A0 ≤ A := geom.coatom_eq ▸ inf_le_left
  have hAP : A ≤ GAt Γ cp.firstStep := hAE.trans geom.group_le
  have hZN : GAt Γ cp.firstStep ≤ Subgroup.normalizer (Z : Set G) :=
    stabilizer_le_normalizer_z Γ cp.firstStep
  have hZaV : ZAt Γ cp.a ≤ V :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hUP : U ≤ V := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨e,z,rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (stabilizer_le_normalizer_v Γ cp.firstStep (geom.group_le e.property)) z).mp
        (hZaV z.property)
  have hZG := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2
  have hZU : Z ≤ U := hZG.trans (by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩)
  have hVP : V ≤ GAt Γ cp.firstStep :=
    (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by exact hlength ▸ by decide) _).trans
      (by change Γ.twoCoreAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
          rw [Γ.twoCoreAt_def]; exact Subgroup.map_subtype_le _)
  have hUnormal : (Z.subgroupOf U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer ((hUP.trans hVP).trans hZN)
  let _ := hUnormal
  obtain ⟨hVnormal,hVelem,_⟩ := eight_six_next_quotient_module_data_local ctx hcenter hlength
    hcard data.first_commutator
  let _ := hVnormal
  let _ := hVelem
  have hUcomm : ⁅U,U⁆ ≤ Z := (Subgroup.commutator_mono hUP
    (hUP.trans (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
      (by exact hlength ▸ by decide) _))).trans_eq data.first_commutator
  have hderived : _root_.commutator U ≤ Z.subgroupOf U := by
    intro u hu
    apply hUcomm
    have hm : (_root_.commutator U).map U.subtype = ⁅U,U⁆ := by
      rw [_root_.commutator_def,Subgroup.map_commutator,
        ← MonoidHom.range_eq_map,Subgroup.range_subtype]
    exact hm ▸ Subgroup.mem_map_of_mem U.subtype hu
  have hUelem : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U) := {
    toIsMulCommutative := (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := Z.subgroupOf U)).mpr hderived
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro u
      obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) u
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      let v : V := ⟨u,hUP u.property⟩
      have hp : (QuotientGroup.mk' (Z.subgroupOf V) v)^2 = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (V ⧸ Z.subgroupOf V)) _
      rw [← map_pow] at hp
      exact (QuotientGroup.eq_one_iff (v ^ 2)).mp hp) }
  have hindex : A0.relIndex A = 2 := by
    have hh := (A0.subgroupOf A).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0A).toEquiv] at hh
    have hcount : Nat.card A = 2 * Nat.card A0 := geom.coatom_card
    change A0.relIndex A * Nat.card A0 = Nat.card A at hh
    have hp : 0 < Nat.card A0 := Nat.card_pos
    nlinarith
  have hfirst := Subgroup.commutator_commutator_le_of_elementary_quotient_index_two
    U Z A0 A hZU
    (hAE.trans (eight_six_conjugate_closure_normalizer (ZAt Γ cp.a) E))
    (hAP.trans hZN) hUnormal hUelem hA0A hindex
    (eight_six_selected_orbit_commutator_le ctx hcenter hcard E A0 geom.group_le
      (hA0A.trans inf_le_right) geom.coatom_commutator)
  have hsecond := eight_six_initial_core_double_actor_commutator_le_previous
    ctx hcenter hlength hcard previous D L Q hprev.1 data U hcore
  have hdisj := (eight_six_neighbor_center_lines ctx hcenter hquot hlength hcard previous hprev).2.2.2
  exact bot_unique ((le_inf hsecond hfirst).trans_eq hdisj.eq_bot)

end Stellmacher.SectionEight
