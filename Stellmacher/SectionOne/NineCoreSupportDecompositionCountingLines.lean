module

public import Stellmacher.SectionOne.NineCoreSupportDecompositionTransport
public import Theory.ElementaryAbelian.Basic

/-!
# Counting the intrinsic supporting lines

The nonidentity elements of an elementary abelian group of order nine
partition into four ambient order-three lines, with two generators per line.
Fixed sets of generators equal the fixed subgroups of their lines. Burnside
counting and the fixed-subgroup cardinality dichotomy imply that exactly two
lines have fixed subgroups of order four.

This is the numerical prerequisite for the intrinsic support decomposition
in Stellmacher (9.1)(8), printed page 47. Complementarity is proved separately.
-/

@[expose] public section

namespace Stellmacher.SectionOne

private abbrev ActorLines {K : Type*} [Group K] (core : Subgroup K) :=
  {line : Subgroup K // line ≤ core ∧ Nat.card line = 3}

private theorem actor_order {K : Type*} [Group K]
    (core : Subgroup K) (helementary : IsElementaryAbelian 3 core)
    (actor : K) (hmem : actor ∈ core) (hne : actor ≠ 1) : orderOf actor = 3 := by
  let _ := helementary
  have hdiv : orderOf actor ∣ 3 := orderOf_dvd_of_pow_eq_one
    (elemPow_eq_one_of_isElementaryAbelian actor hmem)
  exact (Nat.prime_three.eq_one_or_self_of_dvd _ hdiv).resolve_left
    (fun hone => hne (orderOf_eq_one_iff.mp hone))

private theorem generated_line {K : Type*} [Group K] [Finite K]
    (core : Subgroup K) (helementary : IsElementaryAbelian 3 core)
    (line : ActorLines core) (actor : K) (hmem : actor ∈ line.val)
    (hne : actor ≠ 1) : Subgroup.zpowers actor = line.val := by
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
  rw [line.property.2, Nat.card_zpowers,
    actor_order core helementary actor (line.property.1 hmem) hne]

private def generatorMap {K : Type*} [Group K] (core : Subgroup K) :
    (Σ line : ActorLines core, {actor : line.val // actor ≠ 1}) →
      {actor : core // actor ≠ 1} := fun pair =>
  ⟨⟨pair.2.val.val, pair.1.property.1 pair.2.val.property⟩,
    fun heq => pair.2.property
      (Subtype.ext (congrArg (fun point : core => (point : K)) heq))⟩

private theorem generatorMap_bijective {K : Type*} [Group K] [Finite K]
    (core : Subgroup K) (helementary : IsElementaryAbelian 3 core) :
    Function.Bijective (generatorMap core) := by
  constructor
  · rintro ⟨first, actor⟩ ⟨second, other⟩ heq
    have hactor : actor.val.val = other.val.val :=
      congrArg (fun point => point.val.val) heq
    have hne : actor.val.val ≠ 1 := fun hone => actor.property (Subtype.ext hone)
    have hfirst := generated_line core helementary first actor.val.val actor.val.property hne
    have hsecond := generated_line core helementary second actor.val.val
      (hactor ▸ other.val.property) hne
    have hlines : first = second := Subtype.ext (hfirst.symm.trans hsecond)
    subst second
    have hactors : actor = other := Subtype.ext (Subtype.ext hactor)
    subst other
    rfl
  · intro actor
    have hne : actor.val.val ≠ 1 := fun hone => actor.property (Subtype.ext hone)
    let line : ActorLines core := ⟨Subgroup.zpowers actor.val.val,
      Subgroup.zpowers_le.mpr actor.val.property,
      (Nat.card_zpowers _).trans
        (actor_order core helementary _ actor.val.property hne)⟩
    refine ⟨⟨line, ⟨⟨actor.val.val, Subgroup.mem_zpowers _⟩, ?_⟩⟩, rfl⟩
    intro hone
    exact hne (congrArg Subtype.val hone)

private theorem nonidentity_card {G : Type*} [Group G] [Finite G] :
    Nat.card {actor : G // actor ≠ 1} = Nat.card G - 1 := by
  classical
  let _ := Fintype.ofFinite G
  simp only [Nat.card_eq_fintype_card]
  simp

private theorem line_card {K : Type*} [Group K] [Finite K]
    (core : Subgroup K) (helementary : IsElementaryAbelian 3 core)
    (hcard : Nat.card core = 9) : Nat.card (ActorLines core) = 4 := by
  classical
  let _ := Fintype.ofFinite (ActorLines core)
  let _ : ∀ line : ActorLines core, Fintype {actor : line.val // actor ≠ 1} :=
    fun _ => Fintype.ofFinite _
  have hcount := Nat.card_congr
    (Equiv.ofBijective (generatorMap core) (generatorMap_bijective core helementary))
  rw [nonidentity_card, hcard] at hcount
  have hfiber (line : ActorLines core) :
      Nat.card {actor : line.val // actor ≠ 1} = 2 := by
    rw [nonidentity_card, line.property.2]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma] at hcount
  have hfiber' (line : ActorLines core) :
      Fintype.card {actor : line.val // actor ≠ 1} = 2 := by
    simpa only [← Nat.card_eq_fintype_card] using hfiber line
  simp only [hfiber', Finset.sum_const, Finset.card_univ, smul_eq_mul] at hcount
  rw [Nat.card_eq_fintype_card]
  omega

private theorem fixedBy_card {K V : Type*} [Group K] [Group V] [Finite K]
    [MulDistribMulAction K V]
    (core : Subgroup K) (helementary : IsElementaryAbelian 3 core)
    (line : ActorLines core) (actor : line.val) (hne : actor ≠ 1) :
    Nat.card (MulAction.fixedBy V (⟨actor.val, line.property.1 actor.property⟩ : core)) =
      Nat.card (FixedPoints.subgroup line.val V) := by
  have hgen := generated_line core helementary line actor.val actor.property
    (fun hone => hne (Subtype.ext hone))
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro value
  change (actor.val • value = value) ↔ ∀ other : line.val, (other.val • value = value)
  constructor
  · intro hfix other
    have hother : other.val ∈ Subgroup.zpowers actor.val := by
      rw [hgen]
      exact other.property
    exact smul_eq_self_of_mem_zpowers hother hfix
  · intro hfix
    exact hfix actor

private theorem fixedBy_sum {K V : Type*} [Group K] [Group V] [Finite K]
    [Finite V] [MulDistribMulAction K V]
    (core : Subgroup K) (helementary : IsElementaryAbelian 3 core)
    [Fintype core] [Fintype (ActorLines core)] :
    (∑ actor : core, Nat.card (MulAction.fixedBy V actor)) =
      Nat.card V + 2 * ∑ line : ActorLines core,
        Nat.card (FixedPoints.subgroup line.val V) := by
  classical
  let _ : ∀ line : ActorLines core, Fintype {actor : line.val // actor ≠ 1} :=
    fun _ => Fintype.ofFinite _
  let equivalence := Equiv.ofBijective (generatorMap core)
    (generatorMap_bijective core helementary)
  have hsum := Fintype.sum_equiv equivalence
    (fun pair => Nat.card (FixedPoints.subgroup pair.1.val V))
    (fun actor => Nat.card (MulAction.fixedBy V actor.val))
    (fun pair => (fixedBy_card core helementary pair.1 pair.2.val pair.2.property).symm)
  have hfiber (line : ActorLines core) :
      Fintype.card {actor : line.val // actor ≠ 1} = 2 := by
    rw [← Nat.card_eq_fintype_card, nonidentity_card, line.property.2]
  rw [Fintype.sum_sigma] at hsum
  change (∑ line : ActorLines core, ∑ _actor : {actor : line.val // actor ≠ 1},
    Nat.card (FixedPoints.subgroup line.val V)) =
    (∑ actor : {actor : core // actor ≠ 1}, Nat.card (MulAction.fixedBy V actor.val)) at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hfiber] at hsum
  rw [← Finset.mul_sum] at hsum
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun actor : core => actor = 1)
    (fun actor => Nat.card (MulAction.fixedBy V actor))
  let _ : Fintype {actor : core // actor = 1} := Subtype.fintype _
  change (∑ actor : {actor : core // actor = 1}, Nat.card (MulAction.fixedBy V actor.val)) +
    (∑ actor : {actor : core // actor ≠ 1}, Nat.card (MulAction.fixedBy V actor.val)) =
    (∑ actor : core, Nat.card (MulAction.fixedBy V actor)) at hsplit
  have hone : (∑ actor : {actor : core // actor = 1},
      Nat.card (MulAction.fixedBy V actor.val)) = Nat.card V := by
    have hvalue (actor : {actor : core // actor = 1}) :
        Nat.card (MulAction.fixedBy V actor.val) = Nat.card V := by
      rw [actor.property, MulAction.fixedBy_one_eq_univ]
      exact Nat.card_congr (Equiv.Set.univ V)
    rw [Finset.sum_congr rfl (fun actor _ => hvalue actor)]
    simp
  rw [hone, ← hsum] at hsplit
  exact hsplit.symm

theorem nineCoreSupportDecomposition_supporting_lines_card
    {K V : Type*} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (W : Subgroup K) (hWelementary : IsElementaryAbelian 3 W)
    (hWcard : Nat.card W = 9) (hVcard : Nat.card V = 16)
    (hfaith : fixingSubgroup K (Set.univ : Set V) = ⊥) :
    Nat.card {line : Subgroup K // line ≤ W ∧ Nat.card line = 3 ∧
      Nat.card (FixedPoints.subgroup line V) = 4} = 2 := by
  classical
  let _ := Fintype.ofFinite W
  let _ := Fintype.ofFinite (ActorLines W)
  let _ : ∀ actor : W, Fintype (MulAction.fixedBy V actor) :=
    fun _ => Fintype.ofFinite _
  let _ := Fintype.ofFinite (Quotient (MulAction.orbitRel W V))
  let supports := {line : ActorLines W // Nat.card (FixedPoints.subgroup line.val V) = 4}
  let _ := Fintype.ofFinite supports
  have hlines : Nat.card (ActorLines W) = 4 := line_card W hWelementary hWcard
  have hbound : Nat.card supports ≤ 4 := by
    rw [← hlines, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  have hsum : (∑ line : ActorLines W, Nat.card (FixedPoints.subgroup line.val V)) =
      4 + 3 * Nat.card supports := by
    have hterm (line : ActorLines W) : Nat.card (FixedPoints.subgroup line.val V) =
        1 + 3 * (if Nat.card (FixedPoints.subgroup line.val V) = 4 then 1 else 0) := by
      rcases nineCoreSupportDecomposition_line_fixed_card line.val line.property.2 hVcard
        hfaith with hone | hfour
      · rw [hone]
        decide
      · rw [hfour]
        decide
    rw [Finset.sum_congr rfl (fun line _ => hterm line)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hcardSupports : (∑ line : ActorLines W,
        if Nat.card (FixedPoints.subgroup line.val V) = 4 then 1 else 0) =
        Nat.card supports := by
      simp [supports, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcardSupports]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card, hlines]
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group W V
  have hburn' : (∑ actor : W, Nat.card (MulAction.fixedBy V actor)) =
      Nat.card (Quotient (MulAction.orbitRel W V)) * Nat.card W := by
    simpa only [Nat.card_eq_fintype_card] using hburn
  rw [fixedBy_sum W hWelementary, hVcard, hWcard, hsum] at hburn'
  have hdvd : 9 ∣ 24 + 6 * Nat.card supports := by
    have hrew : 24 + 6 * Nat.card supports =
        Nat.card (Quotient (MulAction.orbitRel W V)) * 9 := by omega
    rw [hrew]
    exact dvd_mul_left _ _
  have hsupportCard : Nat.card supports = 2 := by
    omega
  have hequiv : supports ≃ {line : Subgroup K // line ≤ W ∧ Nat.card line = 3 ∧
      Nat.card (FixedPoints.subgroup line V) = 4} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun line : Subgroup K => line ≤ W ∧ Nat.card line = 3)
      (fun line => Nat.card (FixedPoints.subgroup line V) = 4)).trans
      (Equiv.subtypeEquivRight (fun _ => and_assoc))
  exact (Nat.card_congr hequiv).symm.trans hsupportCard

end Stellmacher.SectionOne

