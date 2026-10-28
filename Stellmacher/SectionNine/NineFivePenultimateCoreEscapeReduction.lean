module

public import Stellmacher.SectionNine.NineFivePenultimateJoinAction
public import Stellmacher.SectionNine.NineFiveConjugatorAlgebra
public import Stellmacher.SectionFiveToSeven.ResidualTransport

/-!
# From nontrivial core action to escape from the terminal center

The penultimate residual normalizes the actual commutator enlarged by the
penultimate center. Since that center centralizes both the core and the
commutator, the core commutator itself is residual-invariant. If contained
in the order-two terminal center, it is centralized by the residual.
Transported (7.5)(c) then makes it trivial.

This proves the modulo-terminal-center step in the last paragraph of
Stellmacher (9.5), printed pp.52–53/PDF pp.42–43. It deliberately retains
the independently required nontriviality and residual-join premises;
neither is asserted here without proof. The final core-escape theorem
must discharge them using their separate upstream producers.
-/

open scoped commutatorElement

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_five_normalized_subgroup_in_line_eq_bot
    {G : Type u} [Group G] (acting core line small : Subgroup G)
    (hline : Nat.card line = 2) (hsmall : small ≤ line)
    (hcore : small ≤ core)
    (hnormal : acting ≤ Subgroup.normalizer (small : Set G))
    (hfaithful : core ⊓ Subgroup.centralizer (acting : Set G) = ⊥) :
    small = ⊥ := by
  obtain ⟨point, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : line)).mp hline
  apply bot_unique
  rw [← hfaithful]
  refine le_inf hcore ?_
  intro vector hvector
  rw [Subgroup.mem_centralizer_iff]
  intro actor hactor
  by_cases hone : vector = 1
  · simp [hone]
  have hconj : actor * vector * actor⁻¹ ∈ line :=
    hsmall ((Subgroup.mem_normalizer_iff.mp (hnormal hactor) vector).mp hvector)
  have hconj_ne : actor * vector * actor⁻¹ ≠ 1 := by
    intro heq
    apply hone
    have hcancel := congrArg (fun value : G => actor⁻¹ * value * actor) heq
    simpa [mul_assoc] using hcancel
  have hvector_eq : (⟨vector, hsmall hvector⟩ : line) = point :=
    hunique _ (fun heq => hone (congrArg Subtype.val heq))
  have hconj_eq : (⟨actor * vector * actor⁻¹, hconj⟩ : line) = point :=
    hunique _ (fun heq => hconj_ne (congrArg Subtype.val heq))
  have hcancel := congrArg (fun value : line => (value : G) * actor)
    (hconj_eq.trans hvector_eq.symm)
  simpa [mul_assoc] using hcancel

public theorem nine_five_core_commutator_normalizer
    {G : Type u} [Group G] (acting core residual center : Subgroup G)
    (hcore : acting ≤ Subgroup.normalizer (core : Set G))
    (hjoin : acting ≤ Subgroup.normalizer (↑(residual ⊔ center) : Set G))
    (hcenterCore : ⁅center, core⁆ = ⊥)
    (hcenterResidual : ⁅center, residual⁆ = ⊥) :
    acting ≤ Subgroup.normalizer (↑(⁅core, residual⁆) : Set G) := by
  have hcenterCentral : center ≤ Subgroup.centralizer (↑(core ⊔ residual) : Set G) := by
    apply Subgroup.le_centralizer_iff.mp
    exact sup_le
      (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcenterCore))
      (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcenterResidual))
  have hcenterNorm : center ≤ Subgroup.normalizer (↑(⁅core, residual⁆) : Set G) :=
    (hcenterCentral.trans (Subgroup.centralizer_le (Subgroup.commutator_le_sup _ _))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcomm : ⁅core, residual ⊔ center⁆ = ⁅core, residual⁆ := by
    apply le_antisymm
    · rw [Subgroup.commutator_comm core]
      apply nine_five_commutator_join_le
      · exact Subgroup.normalizer_commutator_ge_right _ _
      · exact hcenterNorm
      · exact (Subgroup.commutator_comm _ _).le
      · exact hcenterCore.le.trans bot_le
    · exact Subgroup.commutator_mono le_rfl le_sup_left
  intro actor hactor
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [← hcomm, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hcore hactor),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hjoin hactor)]

public theorem nine_five_initial_orbit_residual_centralizer
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex) :
    QAt ctx.Γ vertex ⊓ Subgroup.centralizer (EAt ctx.Γ vertex : Set G) = ⊥ := by
  obtain ⟨actor, rfl⟩ := horbit
  let equiv := MulAut.conj actor⁻¹
  have hres : EAt ctx.Γ (ctx.Γ.act actor ctx.criticalPath.a) =
      (EAt ctx.Γ ctx.criticalPath.a).map equiv.toMonoidHom := by
    change ctx.Γ.twoResidualAt _ = (ctx.Γ.twoResidualAt _).map _
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoResidualAt_def]
    change twoResidualIn (stabilizer ctx.Γ (ctx.Γ.act actor ctx.criticalPath.a)) = _
    rw [stabilizer_act, conjugateBy, twoResidualIn_map_equiv]
    rfl
  apply bot_unique
  rintro element ⟨hcore, hcentral⟩
  change element ∈ q ctx.Γ (ctx.Γ.act actor ctx.criticalPath.a) at hcore
  rw [q_act] at hcore
  obtain ⟨original, horiginal, rfl⟩ := hcore
  have hcent : original ∈ Subgroup.centralizer
      (EAt ctx.Γ ctx.criticalPath.a : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro member hmember
    apply equiv.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hcentral (equiv member)
      (hres ▸ Subgroup.mem_map_of_mem equiv.toMonoidHom hmember)
  have hbot : original ∈ (⊥ : Subgroup G) :=
    (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
      ctx.commutator_eq).centralizer_residual ▸ ⟨horiginal, hcent⟩
  exact Subgroup.mem_bot.mpr (by rw [Subgroup.mem_bot.mp hbot, map_one])

public theorem nine_five_penultimate_core_escape_of_initial_four_and_nontrivial
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hb : 1 < ctx.criticalPath.length) (prev : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) prev)
    (actor : G)
    (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hcontain : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
      VAt ctx.Γ prev)
    (hjoin : EAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤ QAt ctx.Γ prev ⊔ QAt ctx.Γ ctx.criticalPath.a')
    (hnontrivial : ⁅twoCoreIn (EAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)),
      ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆⁆ ≠ ⊥) :
    let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    let residual := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆
    ¬ ⁅twoCoreIn (EAt ctx.Γ penultimate), residual⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a' := by
  let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
    Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let residual := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆
  let core := twoCoreIn (EAt ctx.Γ penultimate)
  have hinputs := nine_five_transvection_inputs ctx.toLocalContext hb prev actor
    hactor hindex hcontain
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a') := hinputs.2.1
  have hRV : residual ≤ VAt ctx.Γ ctx.criticalPath.a' := hinputs.2.2.2.2.1.trans inf_le_left
  have hadj := nine_five_penultimate_adjacent ctx.toLocalContext
  have hcenterV : ZAt ctx.Γ penultimate ≤ VAt ctx.Γ ctx.criticalPath.a' := by
    rw [VAt, v, ctx.Γ.vAt_def]
    exact le_sSup ⟨_, (mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm hadj), rfl⟩
  have hcenterCore : ZAt ctx.Γ penultimate ≤ omegaOneCenter (QAt ctx.Γ penultimate) :=
    (lemma_seven_three ctx.sectionSeven ctx.Γ).center_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
  have hcoreQ : core ≤ QAt ctx.Γ penultimate := by
    change twoCoreIn (e ctx.Γ penultimate) ≤ q ctx.Γ penultimate
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, q, ctx.Γ.twoCoreAt_def,
      residual_core_eq_inter_core]
    exact inf_le_right
  have hcentral : ⁅ZAt ctx.Γ penultimate, core⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact (hcenterCore.trans ((omegaOneCenter_le_centerAmbient _).trans
      (centerAmbient_le_centralizer _))).trans (Subgroup.centralizer_le hcoreQ)
  have hcenterResidual : ⁅ZAt ctx.Γ penultimate, residual⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact (hcenterV.trans (Subgroup.le_centralizer _)).trans
      (Subgroup.centralizer_le hRV)
  have hnorm := (nine_five_penultimate_join_action_of_initial_four
    ctx hfour hb prev hpath residual (le_inf hcontain hRV)).2
  have hcommNorm := nine_five_core_commutator_normalizer
    (EAt ctx.Γ penultimate) core residual (ZAt ctx.Γ penultimate)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (twoCoreIn_le _)).mp
      (twoCoreIn_normal _)) (hjoin.trans hnorm) hcentral hcenterResidual
  have hline := (nine_five_penultimate_center_layer_of_initial_four
    ctx.toLocalContext hfour).1
  have hterminalOrbit := nine_five_penultimate_neighbor_orbit ctx.toLocalContext _ hadj
  have hlineCard := (nine_next_center_and_commutator_of_initial_four
    ctx.toLocalContext hfour _ hterminalOrbit).1
  obtain ⟨mover, hmiddle, _⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hfaithful := nine_five_initial_orbit_residual_centralizer
    ctx.toLocalContext penultimate ⟨mover, hmiddle⟩
  change ¬ ⁅core, residual⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a'
  intro hsmall
  exact hnontrivial (nine_five_normalized_subgroup_in_line_eq_bot
    (EAt ctx.Γ penultimate) (QAt ctx.Γ penultimate)
    (ZAt ctx.Γ ctx.criticalPath.a') ⁅core, residual⁆ hlineCard hsmall
    ((hsmall.trans hline).trans (hcenterCore.trans (Subgroup.map_subtype_le _)))
    hcommNorm hfaithful)

end Stellmacher.SectionNine
