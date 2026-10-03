module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexModelSetup

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_initial_residual_core_eq
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    {D Q : Subgroup G} (orders : EightSixSmallIndexOrderData graph path D Q) :
    twoCoreIn (EAt graph path.a) = EAt graph path.a ⊓ Q := by
  rw [orders.core_eq]
  change twoCoreIn (graph.twoResidualAt path.a) =
    graph.twoResidualAt path.a ⊓ graph.twoCoreAt path.a
  rw [graph.twoResidualAt_def, graph.twoCoreAt_def]
  exact SevenSix.residual_core_eq_inter_core _

public theorem eight_six_initial_order_cases
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    {D Q : Subgroup G} (orders : EightSixSmallIndexOrderData graph path D Q)
    (hcard : Nat.card (ZAt graph path.a) = 4) :
    (Nat.card D = 4 ∧ Nat.card Q = 16) ∨
      (Nat.card D = 8 ∧ Nat.card Q = 32) := by
  have hratio := orders.quotient_card
  change Nat.card Q = 4 * Nat.card D at hratio
  rcases orders.center_index with hindex | hindex
  · change Nat.card D = 1 * Nat.card (ZAt graph path.a) at hindex
    rw [hcard] at hindex
    exact Or.inl ⟨by omega, by omega⟩
  · change Nat.card D = 2 * Nat.card (ZAt graph path.a) at hindex
    rw [hcard] at hindex
    exact Or.inr ⟨by omega, by omega⟩

public theorem eight_six_generated_with_of_index_two
    {G : Type u} [Group G] [Finite G]
    {core whole : Subgroup G} (hle : core ≤ whole)
    (hcard : Nat.card whole = 2 * Nat.card core)
    {actor : G} (hactor : actor ∈ whole) (houtside : actor ∉ core) :
    whole = GeneratedWith core actor := by
  have hgenerated : GeneratedWith core actor ≤ whole :=
    sup_le hle ((Subgroup.zpowers_le).mpr hactor)
  have hcore : core ≤ GeneratedWith core actor := le_sup_left
  have hactor_generated : actor ∈ GeneratedWith core actor :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers actor)
  have hindex : core.relIndex whole = 2 := by
    have hcount := (core.subgroupOf whole).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hcount
    change Nat.card core * core.relIndex whole = Nat.card whole at hcount
    have hpositive : 0 < Nat.card core := Nat.card_pos
    nlinarith
  have htower := Subgroup.relIndex_mul_relIndex core (GeneratedWith core actor) whole
    hcore hgenerated
  rw [hindex] at htower
  have hnotone : core.relIndex (GeneratedWith core actor) ≠ 1 := by
    intro hone
    exact houtside (Subgroup.relIndex_eq_one.mp hone hactor_generated)
  have hlast : (GeneratedWith core actor).relIndex whole = 1 := by
    by_contra hlast
    exact Nat.not_prime_of_mul_eq htower hnotone hlast Nat.prime_two
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hlast) hgenerated

public theorem eight_six_inverter_outside_c4_square
    {G : Type u} [Group G] {core : Subgroup G}
    (hmodel : IsModel core (C4 × C4)) {actor : G}
    (hinverts : IsInvertingOn actor core) : actor ∉ core := by
  intro hactor
  obtain ⟨model⟩ := hmodel
  let element : core := model.symm (Multiplicative.ofAdd (1 : ZMod 4), 1)
  have hcommute : (⟨actor, hactor⟩ : core) * element =
      element * ⟨actor, hactor⟩ := by
    apply model.injective
    simp only [map_mul]
    exact mul_comm _ _
  have hcommute_ambient : actor * (element : G) = (element : G) * actor :=
    congrArg Subtype.val hcommute
  have hfixed : actor * (element : G) * actor⁻¹ = element := by
    rw [hcommute_ambient, mul_assoc, mul_inv_cancel, mul_one]
  have helement : element = element⁻¹ := by
    apply Subtype.ext
    exact hfixed.symm.trans (hinverts element element.property)
  have hmodel_element := congrArg model helement
  have hfirst := congrArg Prod.fst hmodel_element
  change (model element).1 = (model (element⁻¹)).1 at hfirst
  simp only [element, map_inv, MulEquiv.apply_symm_apply, Prod.fst_inv] at hfirst
  have hfalse := congrArg Multiplicative.toAdd hfirst
  exact (by decide : (1 : ZMod 4) ≠ -1) hfalse

public theorem eight_six_initial_models_of_core_and_inverter
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    {D Q : Subgroup G} (orders : EightSixSmallIndexOrderData graph path D Q)
    (hcard : Nat.card (ZAt graph path.a) = 4)
    (hcore : IsModel (twoCoreIn (EAt graph path.a)) (C4 × C4))
    (hinverter : Nat.card Q = 32 → ∃ actor : G,
      actor ∈ Q ∧ IsInvertingOn actor (twoCoreIn (EAt graph path.a))) :
    IsModel (twoCoreIn (EAt graph path.a)) (C4 × C4) ∧
      ∃ actor : G,
        (actor = 1 ∨ IsInvertingOn actor (twoCoreIn (EAt graph path.a))) ∧
        Q = GeneratedWith (twoCoreIn (EAt graph path.a)) actor := by
  have hle : twoCoreIn (EAt graph path.a) ≤ Q := by
    rw [eight_six_initial_residual_core_eq graph path orders]
    exact inf_le_right
  refine ⟨hcore, ?_⟩
  rcases eight_six_initial_order_cases graph path orders hcard with hsmall | hlarge
  · exact eight_six_generated_trivially_of_card_sixteen hle hcore hsmall.2
  · obtain ⟨actor, hactor, hinverts⟩ := hinverter hlarge.2
    have houtside := eight_six_inverter_outside_c4_square hcore hinverts
    have hcorecard : Nat.card (twoCoreIn (EAt graph path.a)) = 16 := by
      obtain ⟨model⟩ := hcore
      rw [Nat.card_congr model.toEquiv, Nat.card_prod]
      simp [C4]
    exact ⟨actor, Or.inr hinverts, eight_six_generated_with_of_index_two hle
      (by rw [hlarge.2, hcorecard]) hactor houtside⟩

end Stellmacher.SectionEight
