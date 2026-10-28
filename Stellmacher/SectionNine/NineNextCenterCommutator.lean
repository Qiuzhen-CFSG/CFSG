module

public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6
public import Stellmacher.SectionFiveToSeven.NeighborModuleNormalClosure
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# Next-center order and module commutator after Stellmacher (9.3)

The four-element initial center suffices for these two consequences of the
initial-orbit model. By (7.6), the next core does not lie in the initial core,
so (7.4) makes its action on the initial center nontrivial. By (7.5), the
next center is the nontrivial Sylow omega-center, contained in the initial
center. Equality would make that next-core action trivial. Thus the next
center is a proper nontrivial subgroup of a group of order four and has
order two.

The next core normalizes both centers, so it acts trivially on their
index-two quotient. Its nontrivial commutator is therefore exactly the
next center. Normal closure in the next stabilizer propagates this equality
to the full neighbor module, using normality of the next core and center.
Graph covariance gives the result at every vertex in the next orbit.

The final ambient theorem retains the precise initial-orbit model and
length assumptions. The stronger local helpers require only the initial
center order. No Hypothesis Two on the generated group is introduced, and
no quotient-kernel or faithfulness argument is duplicated here.

Source: `refs/files/stellmacher-n-group.pdf`, printed p.50/PDF p.40,
the remark immediately after (9.3). The proof uses an index-two action
argument in place of the remark's intermediate edge core-product identity.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement

universe u

private theorem omega_center_nontrivial
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (hS : IsPGroup 2 S) (hne : S ≠ ⊥) :
    omegaOneCenter S ≠ ⊥ := by
  let _ : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hne
  let _ : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  obtain ⟨power, hpos, hcard⟩ :=
    (hS.to_subgroup (Subgroup.center S)).nontrivial_iff_card.mp inferInstance
  have hdiv : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hpos)
  have hinner := omega₁_map_subtype_ne_bot (G := S) (Subgroup.center S) 2 hdiv
  intro hbot
  apply hinner
  apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
  simpa [omegaOneCenter] using hbot

private theorem next_core_not_le_initial_core
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    ¬ QAt ctx.Γ ctx.criticalPath.firstStep ≤ QAt ctx.Γ ctx.criticalPath.a := by
  intro hle
  apply (lemma_seven_six ctx.sectionSeven ctx.Γ ctx.criticalPath).next_residual_core.1
  apply le_trans ?_ hle
  change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.firstStep) ≤
    ctx.Γ.twoCoreAt ctx.criticalPath.firstStep
  rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def, residual_core_eq_inter_core]
  exact inf_le_right

public theorem nine_initial_next_core_commutator_ne_bot
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    ⁅ZAt ctx.Γ ctx.criticalPath.a, QAt ctx.Γ ctx.criticalPath.firstStep⁆ ≠ ⊥ := by
  intro hbot
  apply next_core_not_le_initial_core ctx
  change q ctx.Γ ctx.criticalPath.firstStep ≤ q ctx.Γ ctx.criticalPath.a
  rw [← (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).edge_centralizer]
  exact le_inf (local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
    (Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot))

private theorem next_center_le_initial_center
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    ZAt ctx.Γ ctx.criticalPath.firstStep ≤ ZAt ctx.Γ ctx.criticalPath.a := by
  change z ctx.Γ ctx.criticalPath.firstStep ≤ z ctx.Γ ctx.criticalPath.a
  rw [(lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).next_center.1]
  obtain ⟨_, sylow, hsylow⟩ := (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  rw [z, ctx.Γ.zAt_def]
  exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩

public theorem nine_next_center_order_of_initial_four
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.firstStep) = 2 := by
  have hle := next_center_le_initial_center ctx
  have hne : ZAt ctx.Γ ctx.criticalPath.firstStep ≠ ⊥ := by
    change z ctx.Γ ctx.criticalPath.firstStep ≠ ⊥
    rw [(lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).next_center.1]
    exact omega_center_nontrivial T
      (sectionThreeHypotheses ctx.sectionSeven).nontrivial_two_subgroup.2
      ctx.sectionSeven.S_nontrivial
  have hnotFour : Nat.card (ZAt ctx.Γ ctx.criticalPath.firstStep) ≠ 4 := by
    intro hcard
    have heq := Subgroup.eq_of_le_of_card_ge hle (by omega)
    apply nine_initial_next_core_commutator_ne_bot ctx
    rw [← heq, Subgroup.commutator_eq_bot_iff_le_centralizer]
    change z ctx.Γ ctx.criticalPath.firstStep ≤ _
    rw [(lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).next_center.2]
    exact ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _)).trans
      (Subgroup.centralizer_le (show (QAt ctx.Γ ctx.criticalPath.firstStep : Set G) ⊆
        GAt ctx.Γ ctx.criticalPath.firstStep from by
          change q ctx.Γ ctx.criticalPath.firstStep ≤ stabilizer ctx.Γ ctx.criticalPath.firstStep
          rw [q, ctx.Γ.twoCoreAt_def]
          exact Subgroup.map_subtype_le _))
  have hdiv := Subgroup.card_dvd_of_le hle
  rw [hfour] at hdiv
  have hpos := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have hbound := Nat.le_of_dvd (by decide : 0 < 4) hdiv
  interval_cases card : Nat.card (ZAt ctx.Γ ctx.criticalPath.firstStep) <;> norm_num at *

private theorem commutator_le_of_index_two
    {G : Type u} [Group G] [Finite G] (large small actor : Subgroup G)
    (hindex : (small.subgroupOf large).index = 2)
    (hnlarge : actor ≤ Subgroup.normalizer (large : Set G))
    (hnsmall : actor ≤ Subgroup.normalizer (small : Set G)) :
    ⁅large, actor⁆ ≤ small := by
  apply Subgroup.commutator_le.mpr
  intro vector hvector mover hmover
  have hconj : mover * vector⁻¹ * mover⁻¹ ∈ large :=
    (Subgroup.mem_normalizer_iff.mp (hnlarge hmover) _).mp (large.inv_mem hvector)
  have hsame : (⟨vector, hvector⟩ : large) ∈ small.subgroupOf large ↔
      (⟨mover * vector⁻¹ * mover⁻¹, hconj⟩ : large) ∈ small.subgroupOf large := by
    change vector ∈ small ↔ mover * vector⁻¹ * mover⁻¹ ∈ small
    exact small.inv_mem_iff.symm.trans
      (Subgroup.mem_normalizer_iff.mp (hnsmall hmover) _)
  have hm := ((small.subgroupOf large).mul_mem_iff_of_index_two hindex).mpr hsame
  change vector * (mover * vector⁻¹ * mover⁻¹) ∈ small at hm
  simpa only [commutatorElement_def, mul_assoc] using hm

public theorem nine_initial_next_core_commutator_of_initial_four
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    ⁅ZAt ctx.Γ ctx.criticalPath.a, QAt ctx.Γ ctx.criticalPath.firstStep⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  have htwo := nine_next_center_order_of_initial_four ctx hfour
  have hle := next_center_le_initial_center ctx
  have hindex : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (ZAt ctx.Γ ctx.criticalPath.a)).index = 2 := by
    have hcard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hprod := ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (ZAt ctx.Γ ctx.criticalPath.a)).index_mul_card
    rw [hcard, htwo, hfour] at hprod
    omega
  have hQP : QAt ctx.Γ ctx.criticalPath.firstStep ≤ GAt ctx.Γ ctx.criticalPath.firstStep := by
    rw [QAt, q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hcommle := commutator_le_of_index_two
    (ZAt ctx.Γ ctx.criticalPath.a) (ZAt ctx.Γ ctx.criticalPath.firstStep)
    (QAt ctx.Γ ctx.criticalPath.firstStep) hindex
    (((local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2.trans
      (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1).trans
        (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a))
    (hQP.trans (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.firstStep))
  apply Subgroup.eq_of_le_of_card_ge hcommle
  rw [htwo]
  exact (Subgroup.one_lt_card_iff_ne_bot _).mpr
    (nine_initial_next_core_commutator_ne_bot ctx)

public theorem nine_next_module_commutator_of_initial_four
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep, QAt ctx.Γ ctx.criticalPath.firstStep⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  let Q := QAt ctx.Γ ctx.criticalPath.firstStep
  let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
  let initial := ZAt ctx.Γ ctx.criticalPath.a
  have hQP : Q ≤ P := by
    change q ctx.Γ ctx.criticalPath.firstStep ≤ stabilizer ctx.Γ ctx.criticalPath.firstStep
    rw [q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZP : Z ≤ P := by
    change z ctx.Γ ctx.criticalPath.firstStep ≤ stabilizer ctx.Γ ctx.criticalPath.firstStep
    rw [(lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).next_center.2]
    exact Subgroup.map_subtype_le _
  have hInitialP : initial ≤ P := by
    have hneighbor := (mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
    exact ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core _ _ hneighbor).trans
      ((Subgroup.map_subtype_le _).trans
        ((local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).1.trans
          (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2.1))
  let _ : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr
      (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.firstStep)
  let _ : (Z.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZP).mpr
      (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.firstStep)
  have hbase : ⁅initial, Q⁆ = Z := nine_initial_next_core_commutator_of_initial_four ctx hfour
  have hbaseNative : ⁅Q.subgroupOf P, initial.subgroupOf P⁆ ≤ Z.subgroupOf P := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQP,
      Subgroup.map_subgroupOf_eq_of_le hInitialP, Subgroup.map_subgroupOf_eq_of_le hZP,
      Subgroup.commutator_comm, hbase]
  have hclosure := Subgroup.map_mono (f := P.subtype)
    (Subgroup.commutator_normalClosure_le_of_normal
      (Q.subgroupOf P) (initial.subgroupOf P) (Z.subgroupOf P) hbaseNative)
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQP,
    Subgroup.map_subgroupOf_eq_of_le hZP, Subgroup.commutator_comm] at hclosure
  have hmodule := neighbor_module_eq_normalClosure_center ctx.sectionSeven ctx.Γ
    ctx.criticalPath.a ctx.criticalPath.firstStep ctx.criticalPath.firstStep_adj
  change v ctx.Γ ctx.criticalPath.firstStep = _ at hmodule
  change ⁅v ctx.Γ ctx.criticalPath.firstStep, Q⁆ = Z
  refine le_antisymm ?_ ?_
  · rw [hmodule]
    exact hclosure
  · rw [← hbase]
    exact Subgroup.commutator_mono
      (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1 le_rfl

public theorem nine_next_center_and_commutator_of_initial_four
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex) :
    Nat.card (ZAt ctx.Γ vertex) = 2 ∧
      ⁅VAt ctx.Γ vertex, QAt ctx.Γ vertex⁆ = ZAt ctx.Γ vertex := by
  obtain ⟨actor, rfl⟩ := horbit
  change Nat.card (z ctx.Γ (ctx.Γ.act actor ctx.criticalPath.firstStep)) = 2 ∧
    ⁅v ctx.Γ (ctx.Γ.act actor ctx.criticalPath.firstStep),
      q ctx.Γ (ctx.Γ.act actor ctx.criticalPath.firstStep)⁆ =
      z ctx.Γ (ctx.Γ.act actor ctx.criticalPath.firstStep)
  rw [z_act, v_act, q_act, ← Subgroup.map_commutator]
  constructor
  · exact (Nat.card_congr ((z ctx.Γ ctx.criticalPath.firstStep).equivMapOfInjective
      (MulAut.conj actor⁻¹).toMonoidHom (MulAut.conj actor⁻¹).injective).toEquiv).symm.trans
      (nine_next_center_order_of_initial_four ctx hfour)
  · exact congrArg (fun subgroup : Subgroup G => subgroup.map (MulAut.conj actor⁻¹).toMonoidHom)
      (nine_next_module_commutator_of_initial_four ctx hfour)

public theorem nine_next_center_and_commutator_of_initial_model
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (_hb : 1 < ctx.criticalPath.length)
    (hmodel : ∀ vertex : ctx.Γ.Vertex,
      IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
        QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two ∧
          Nat.card (ZAt ctx.Γ vertex) = 4)
    (d : ctx.Γ.Vertex)
    (hd : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep d) :
    Nat.card (ZAt ctx.Γ d) = 2 ∧ ⁅VAt ctx.Γ d, QAt ctx.Γ d⁆ = ZAt ctx.Γ d := by
  exact nine_next_center_and_commutator_of_initial_four ctx.toLocalContext
    (hmodel ctx.criticalPath.a ⟨1, ctx.Γ.act_one _⟩).2 d hd

end Stellmacher.SectionNine
