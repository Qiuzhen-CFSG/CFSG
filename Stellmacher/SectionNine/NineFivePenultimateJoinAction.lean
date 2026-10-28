module

public import Stellmacher.SectionNine.NineFiveSpanAlgebra
public import Stellmacher.SectionNine.NineNextCenterCommutator
public import Stellmacher.SectionNine.NineSevenCenterJoin
public import Stellmacher.SectionNine.NineThreeOrbitModuleCentralizer

/-!
# The penultimate two-core join in Stellmacher (9.5)

For the preceding and terminal vertices, every subgroup of their common
neighbor modules has its commutator with the join of their two-cores in the
penultimate center. Its product with that center is normal in the join.
The sole model input is the initial center's order four, whose unconditional
producer is the separate ambient (9.3) task. These are the first assertions
of the final paragraph of (9.5), printed p.52/PDF p.42.

This module does not assert the missing containment of the penultimate
residual in the join, or the core commutator's escape from the terminal
center. In particular it is not the unconditional core-action theorem.
-/

open scoped commutatorElement IsMulCommutative

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_five_commutator_join_le
    {G : Type u} [Group G] (left right residual layer : Subgroup G)
    (hleft : left ≤ Subgroup.normalizer (layer : Set G))
    (hright : right ≤ Subgroup.normalizer (layer : Set G))
    (hleftcomm : ⁅left, residual⁆ ≤ layer)
    (hrightcomm : ⁅right, residual⁆ ≤ layer) :
    ⁅left ⊔ right, residual⁆ ≤ layer := by
  let actors : Subgroup G :=
    { carrier := {element | element ∈ Subgroup.normalizer (layer : Set G) ∧
        ∀ vector ∈ residual, ⁅element, vector⁆ ∈ layer}
      one_mem' := ⟨(Subgroup.normalizer (layer : Set G)).one_mem, by simp⟩
      mul_mem' := by
        rintro first second ⟨hfirst, hfirstcomm⟩ ⟨hsecond, hsecondcomm⟩
        refine ⟨(Subgroup.normalizer (layer : Set G)).mul_mem hfirst hsecond, ?_⟩
        intro vector hvector
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact layer.mul_mem
          (Subgroup.le_normalizer_iff.mp le_rfl first hfirst _ (hsecondcomm vector hvector))
          (hfirstcomm vector hvector)
      inv_mem' := by
        rintro element ⟨helement, hcomm⟩
        refine ⟨(Subgroup.normalizer (layer : Set G)).inv_mem helement, ?_⟩
        intro vector hvector
        rw [commutatorElement_inv_left]
        have hinv : ⁅vector, element⁆ ∈ layer := by
          rw [← commutatorElement_inv]
          exact layer.inv_mem (hcomm vector hvector)
        simpa only [inv_inv] using
          Subgroup.le_normalizer_iff.mp le_rfl element⁻¹
            ((Subgroup.normalizer (layer : Set G)).inv_mem helement) _ hinv }
  have hleftactors : left ≤ actors := fun element helement =>
    ⟨hleft helement, Subgroup.commutator_le.mp hleftcomm element helement⟩
  have hrightactors : right ≤ actors := fun element helement =>
    ⟨hright helement, Subgroup.commutator_le.mp hrightcomm element helement⟩
  exact Subgroup.commutator_le.mpr fun element helement =>
    ((sup_le hleftactors hrightactors) helement).2

public theorem nine_five_previous_adjacent_penultimate
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length) (prev : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) prev) :
    ctx.Γ.adjacent prev
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  obtain ⟨index, hindex, rfl⟩ := hpath
  have hedge := ctx.criticalPath.path_adj ⟨ctx.criticalPath.length - 2, by omega⟩
  convert hedge using 1 <;> apply congrArg ctx.criticalPath.path <;> apply Fin.ext <;> simp <;> omega

public theorem nine_five_penultimate_neighbor_orbit
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (neighbor : ctx.Γ.Vertex)
    (hadj : ctx.Γ.adjacent
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) neighbor) :
    IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep neighbor := by
  obtain ⟨mover, hmiddle, hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  obtain ⟨wheel, hwheel⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    _ ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (nine_five_penultimate_adjacent ctx))
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
  exact ⟨mover * (wheel : G), by rw [ctx.Γ.act_mul, hterminal, hwheel]⟩

public theorem nine_five_penultimate_join_action_of_initial_four
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hb : 1 < ctx.criticalPath.length) (prev : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) prev)
    (residual : Subgroup G)
    (hresidual : residual ≤ VAt ctx.Γ prev ⊓ VAt ctx.Γ ctx.criticalPath.a') :
    let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    let joint := QAt ctx.Γ prev ⊔ QAt ctx.Γ ctx.criticalPath.a'
    ⁅joint, residual⁆ ≤ ZAt ctx.Γ penultimate ∧
      joint ≤ Subgroup.normalizer (↑(residual ⊔ ZAt ctx.Γ penultimate) : Set G) := by
  let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
    Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hprev := ctx.Γ.adjacent_symm
    (nine_five_previous_adjacent_penultimate ctx.toLocalContext hb prev hpath)
  have hterminal := nine_five_penultimate_adjacent ctx.toLocalContext
  obtain ⟨mover, hmover, _⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hcenters := (nine_seven_center_join ctx penultimate ⟨mover, hmover⟩).2
  have hneighbor : ∀ vertex, ctx.Γ.adjacent penultimate vertex →
      QAt ctx.Γ vertex ≤ Subgroup.normalizer (ZAt ctx.Γ penultimate : Set G) ∧
        ⁅VAt ctx.Γ vertex, QAt ctx.Γ vertex⁆ ≤ ZAt ctx.Γ penultimate := by
    intro vertex hadj
    have hcore := ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core
      vertex penultimate ((mem_neighborhood_iff_adjacent ctx.Γ).mpr
        (ctx.Γ.adjacent_symm hadj)) (default : Sylow 2
          (stabilizer ctx.Γ vertex ⊓ stabilizer ctx.Γ penultimate : Subgroup G))).2.2
    refine ⟨hcore.trans (stabilizer_le_normalizer_z ctx.Γ penultimate), ?_⟩
    exact (nine_next_center_and_commutator_of_initial_four ctx.toLocalContext hfour vertex
      (nine_five_penultimate_neighbor_orbit ctx.toLocalContext vertex hadj)).2.le.trans
        (hcenters vertex ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)).2
  obtain ⟨hprevnorm, hprevcomm⟩ := hneighbor prev hprev
  obtain ⟨hterminalnorm, hterminalcomm⟩ := hneighbor ctx.criticalPath.a' hterminal
  have hbound : ⁅QAt ctx.Γ prev ⊔ QAt ctx.Γ ctx.criticalPath.a', residual⁆ ≤
      ZAt ctx.Γ penultimate := by
    apply nine_five_commutator_join_le _ _ _ _ hprevnorm hterminalnorm
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono (hresidual.trans inf_le_left) le_rfl).trans hprevcomm
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono (hresidual.trans inf_le_right) le_rfl).trans hterminalcomm
  refine ⟨hbound, ?_⟩
  apply Subgroup.le_normalizer_iff_commutator_le_right.mpr
  rw [Subgroup.commutator_comm]
  apply nine_five_commutator_join_le _ _ _ _
  · exact le_sup_left.trans Subgroup.le_normalizer
  · exact le_sup_right.trans Subgroup.le_normalizer
  · rw [Subgroup.commutator_comm]
    exact hbound.trans le_sup_right
  · rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_right.mp
      (sup_le hprevnorm hterminalnorm)).trans le_sup_right

public theorem nine_five_penultimate_join_normal_of_initial_four
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hb : 1 < ctx.criticalPath.length) (prev : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) prev)
    (residual : Subgroup G)
    (hresidual : residual ≤ VAt ctx.Γ prev ⊓ VAt ctx.Γ ctx.criticalPath.a') :
    let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    let joint := QAt ctx.Γ prev ⊔ QAt ctx.Γ ctx.criticalPath.a'
    IsNormalIn (residual ⊔ ZAt ctx.Γ penultimate) joint ∧
      ⁅joint, residual⁆ ≤ ZAt ctx.Γ penultimate := by
  obtain ⟨hbound, hnormalizer⟩ := nine_five_penultimate_join_action_of_initial_four
    ctx hfour hb prev hpath residual hresidual
  have helementary := (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.2.1
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a') := helementary
  have hmodule : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.a' := by
    apply le_trans ?_ (nine_three_module_centralizer_core_at_vertex ctx ctx.criticalPath.a'
      (nine_five_penultimate_neighbor_orbit ctx.toLocalContext ctx.criticalPath.a'
        (nine_five_penultimate_adjacent ctx.toLocalContext)))
    intro vector hvector
    rw [Subgroup.mem_centralizer_iff]
    intro other hother
    exact congrArg Subtype.val (mul_comm
      (⟨other, hother⟩ : VAt ctx.Γ ctx.criticalPath.a')
      (⟨vector, hvector⟩ : VAt ctx.Γ ctx.criticalPath.a'))
  have hcenter : ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤ VAt ctx.Γ ctx.criticalPath.a' := by
    rw [VAt, v, ctx.Γ.vAt_def]
    exact le_sSup ⟨_, (mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm (nine_five_penultimate_adjacent ctx.toLocalContext)), rfl⟩
  have hle := (sup_le (hresidual.trans inf_le_right) hcenter).trans
    (hmodule.trans (le_sup_right : QAt ctx.Γ ctx.criticalPath.a' ≤
      QAt ctx.Γ prev ⊔ QAt ctx.Γ ctx.criticalPath.a'))
  exact ⟨⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnormalizer⟩, hbound⟩

public theorem nine_five_penultimate_core_bound_of_initial_four_and_residual_join
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
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤ QAt ctx.Γ prev ⊔ QAt ctx.Γ ctx.criticalPath.a') :
    let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    let residual := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆
    ⁅twoCoreIn (EAt ctx.Γ penultimate), residual⁆ ≤ ZAt ctx.Γ penultimate := by
  have hresidual := (nine_five_transvection_inputs ctx.toLocalContext hb prev actor
    hactor hindex hcontain).2.2.2.2.1
  have hbound := (nine_five_penultimate_join_action_of_initial_four ctx hfour hb prev hpath
    _ (le_inf hcontain (hresidual.trans inf_le_left))).1
  exact (Subgroup.commutator_mono ((twoCoreIn_le _).trans hjoin) le_rfl).trans hbound

end Stellmacher.SectionNine
