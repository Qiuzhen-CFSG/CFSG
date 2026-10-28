module

public import Stellmacher.LaterDefs
public import Stellmacher.SectionEight.C4SquareAutomorphismRigidity
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index

namespace Stellmacher.SectionEight

set_option linter.style.haveILetI false

open Later SectionsFiveToSeven

universe u

private theorem normalIn_conj_mem
    {G : Type u} [Group G] {part overgroup : Subgroup G}
    (hnormal : NormalIn part overgroup) {actor element : G}
    (hactor : actor ∈ overgroup) (helement : element ∈ part) :
    actor * element * actor⁻¹ ∈ part :=
  ((Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp
    hnormal.2 hactor element).mp helement

private theorem normalIn_conj_mem_iff
    {G : Type u} [Group G] {part overgroup : Subgroup G}
    (hnormal : NormalIn part overgroup) {actor element : G}
    (hactor : actor ∈ overgroup) :
    actor * element * actor⁻¹ ∈ part ↔ element ∈ part :=
  ((Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp
    hnormal.2 hactor element).symm

public theorem elementary_eight_conjugate_difference_mem
    {G : Type u} [Group G] [Finite G] {overgroup core D Z : Subgroup G}
    (hcore : NormalIn core overgroup) (hD : NormalIn D overgroup)
    (hcardD : Nat.card D = 8) (hcardZ : Nat.card Z = 4)
    (hinter : D ⊓ core = Z) {actor conjugator : G}
    (hactor : actor ∈ D) (hconjugator : conjugator ∈ overgroup) :
    (conjugator * actor * conjugator⁻¹) * actor⁻¹ ∈ Z := by
  have hZD : Z ≤ D := hinter ▸ inf_le_left
  have hindex : (Z.subgroupOf D).index = 2 := by
    have hcount := (Z.subgroupOf D).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv,
      hcardD, hcardZ] at hcount
    omega
  have hconjD := normalIn_conj_mem hD hconjugator hactor
  have hconjZ : conjugator * actor * conjugator⁻¹ ∈ Z ↔ actor ∈ Z := by
    rw [← hinter]
    simp only [Subgroup.mem_inf, hconjD, hactor, true_and]
    exact normalIn_conj_mem_iff hcore hconjugator
  have hproduct := (Z.subgroupOf D).mul_mem_iff_of_index_two hindex
    (a := ⟨conjugator * actor * conjugator⁻¹, hconjD⟩)
    (b := (⟨actor, hactor⟩ : D)⁻¹)
  exact hproduct.mpr (hconjZ.trans Z.inv_mem_iff.symm)

private noncomputable def localCoreAction
    {G : Type u} [Group G] {overgroup core : Subgroup G}
    (hcore : NormalIn core overgroup) (actor : G) (hactor : actor ∈ overgroup) :
    MulAut core :=
  core.normalizerMonoidHom
    ⟨actor, (Subgroup.normal_subgroupOf_iff_le_normalizer hcore.1).mp hcore.2 hactor⟩

private theorem localCoreAction_apply
    {G : Type u} [Group G] {overgroup core : Subgroup G}
    (hcore : NormalIn core overgroup) (actor : G) (hactor : actor ∈ overgroup)
    (element : core) :
    (localCoreAction hcore actor hactor element : G) =
      actor * (element : G) * actor⁻¹ := rfl

public theorem elementary_eight_core_action_commutes
    {G : Type u} [Group G] [Finite G] {overgroup core D Z : Subgroup G}
    (hcore : NormalIn core overgroup) (hD : NormalIn D overgroup)
    (hmodel : IsModel core (C4 × C4))
    (hcardD : Nat.card D = 8) (hcardZ : Nat.card Z = 4)
    (hinter : D ⊓ core = Z) {actor conjugator element : G}
    (hactor : actor ∈ D) (hconjugator : conjugator ∈ overgroup)
    (helement : element ∈ core) :
    actor * (conjugator * element * conjugator⁻¹) * actor⁻¹ =
      conjugator * (actor * element * actor⁻¹) * conjugator⁻¹ := by
  obtain ⟨model⟩ := hmodel
  have hcomm (left right : G) (hleft : left ∈ core) (hright : right ∈ core) :
      left * right = right * left := by
    have heq : (⟨left, hleft⟩ : core) * ⟨right, hright⟩ =
        ⟨right, hright⟩ * ⟨left, hleft⟩ := by
      apply model.injective
      simp only [map_mul]
      exact mul_comm _ _
    exact congrArg Subtype.val heq
  have hdifference := elementary_eight_conjugate_difference_mem
    hcore hD hcardD hcardZ hinter hactor hconjugator
  have hZcore : Z ≤ core := hinter ▸ inf_le_right
  have hacted := normalIn_conj_mem hcore (hD.1 hactor)
    (normalIn_conj_mem hcore hconjugator helement)
  have hcentral := hcomm _ _ (hZcore hdifference) hacted
  have heq :
      (conjugator * actor * conjugator⁻¹) *
          (conjugator * element * conjugator⁻¹) *
          (conjugator * actor * conjugator⁻¹)⁻¹ =
        actor * (conjugator * element * conjugator⁻¹) * actor⁻¹ := by
    calc
      _ = ((conjugator * actor * conjugator⁻¹) * actor⁻¹) *
          (actor * (conjugator * element * conjugator⁻¹) * actor⁻¹) *
          ((conjugator * actor * conjugator⁻¹) * actor⁻¹)⁻¹ := by group
      _ = _ := by rw [hcentral]; group
  calc
    _ = (conjugator * actor * conjugator⁻¹) *
        (conjugator * element * conjugator⁻¹) *
        (conjugator * actor * conjugator⁻¹)⁻¹ := heq.symm
    _ = _ := by group

public theorem c4_square_elementary_eight_action_lifts
    {G : Type u} [Group G] [Finite G] {overgroup core D Z : Subgroup G}
    (hcore : NormalIn core overgroup) (hD : NormalIn D overgroup)
    (hmodel : IsModel core (C4 × C4))
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (hcardD : Nat.card D = 8) (hcardZ : Nat.card Z = 4)
    (hinter : D ⊓ core = Z)
    (hfull : ∀ symmetry : MulAut Z, ∃ conjugator : G,
      conjugator ∈ overgroup ∧ ∀ element : Z,
        conjugator * (element : G) * conjugator⁻¹ = (symmetry element : G))
    {actor : G} (hactor : actor ∈ D) :
    ∃ action : MulAut core,
      (∀ element : core, (action element : G) = actor * (element : G) * actor⁻¹) ∧
      (∀ element : Z.subgroupOf core, action (element : core) = (element : core)) ∧
      ∀ symmetry : MulAut (Z.subgroupOf core), ∃ lift : MulAut core,
        (∀ element : Z.subgroupOf core,
          lift (element : core) = (symmetry element : core)) ∧
        ∀ element : core, action (lift element) = lift (action element) := by
  letI : IsElementaryAbelian 2 D := helementary
  have hZD : Z ≤ D := hinter ▸ inf_le_left
  have hZcore : Z ≤ core := hinter ▸ inf_le_right
  refine ⟨localCoreAction hcore actor (hD.1 hactor),
    localCoreAction_apply hcore actor (hD.1 hactor), ?_, ?_⟩
  · intro element
    apply Subtype.ext
    have hcomm : actor * ((element : core) : G) = ((element : core) : G) * actor :=
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := D)).comm
        (⟨actor, hactor⟩ : D) ⟨(element : core), hZD element.property⟩)
    change actor * ((element : core) : G) * actor⁻¹ = ((element : core) : G)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  · intro symmetry
    let centerEquiv : Z.subgroupOf core ≃* Z := Subgroup.subgroupOfEquivOfLe hZcore
    obtain ⟨conjugator, hconjugator, hrealize⟩ :=
      hfull (centerEquiv.symm.trans (symmetry.trans centerEquiv))
    refine ⟨localCoreAction hcore conjugator hconjugator, ?_, ?_⟩
    · intro element
      apply Subtype.ext
      have hrealizeElement := hrealize (centerEquiv element)
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at hrealizeElement
      exact hrealizeElement
    · intro element
      apply Subtype.ext
      exact elementary_eight_core_action_commutes hcore hD hmodel hcardD hcardZ
        hinter hactor hconjugator element.property

public theorem c4_square_elementary_eight_action
    {G : Type u} [Group G] [Finite G] {overgroup core D Z : Subgroup G}
    (hcore : NormalIn core overgroup) (hD : NormalIn D overgroup)
    (hmodel : IsModel core (C4 × C4))
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (hcardD : Nat.card D = 8) (hcardZ : Nat.card Z = 4)
    (hinter : D ⊓ core = Z)
    (hfull : ∀ symmetry : MulAut Z, ∃ actor : G,
      actor ∈ overgroup ∧ ∀ element : Z,
        actor * (element : G) * actor⁻¹ = (symmetry element : G)) :
    ∀ actor : G, actor ∈ D →
      (∀ element : G, element ∈ core →
        actor * element * actor⁻¹ = element) ∨ IsInvertingOn actor core := by
  obtain ⟨model⟩ := hmodel
  let _ : CommGroup core := model.toMonoidHom.commGroupOfInjective model.injective
  letI : IsElementaryAbelian 2 D := helementary
  have hZD : Z ≤ D := hinter ▸ inf_le_left
  have hZcore : Z ≤ core := hinter ▸ inf_le_right
  have hZcard : Nat.card (Z.subgroupOf core) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZcore).toEquiv, hcardZ]
  intro actor hactor
  obtain ⟨action, haction, hfix, hlifts⟩ :=
    c4_square_elementary_eight_action_lifts (hcore := hcore) (hD := hD)
      (hmodel := ⟨model⟩) (helementary := helementary) (hcardD := hcardD)
      (hcardZ := hcardZ) (hinter := hinter) (hfull := hfull) hactor
  have hsquare : ∀ z : Z.subgroupOf core, (z : core) ^ 2 = 1 := by
    intro z
    apply Subtype.ext
    have hzD : (z : G) ∈ D := hZD (Subgroup.mem_subgroupOf.mp z.property)
    have hp := elemPow_eq_one_of_isElementaryAbelian (p := 2) (G := G) (A := D) (z : G) hzD
    simpa using congrArg (fun element : G => element) hp
  obtain hidentity | hinversion := c4_square_automorphism_rigidity
    model (Z.subgroupOf core) hZcard hsquare action hfix hlifts
  · left
    intro element helement
    have hactionElement := haction ⟨element, helement⟩
    have hid := hidentity ⟨element, helement⟩
    exact hactionElement.symm.trans (by simpa using congrArg Subtype.val hid)
  · right
    intro element helement
    have hactionElement := haction ⟨element, helement⟩
    have hinv := hinversion ⟨element, helement⟩
    calc
      actor * element * actor⁻¹ = (action ⟨element, helement⟩ : G) := hactionElement.symm
      _ = ((⟨element, helement⟩ : core)⁻¹ : core) := by
        simpa using congrArg Subtype.val hinv
      _ = element⁻¹ := rfl

end Stellmacher.SectionEight
