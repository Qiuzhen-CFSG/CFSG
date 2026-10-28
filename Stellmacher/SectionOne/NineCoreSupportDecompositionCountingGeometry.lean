module

public import Stellmacher.SectionOne.NineCoreSupportDecompositionTransport
public import Theory.GroupAction.CoprimeHall
public import Theory.Representation.FourGroupMatrixCoordinates
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Geometry of the intrinsic elementary-nine supports

A faithful group of order nine acting on an elementary abelian group of
order sixteen has trivial common fixed subgroup. Two distinct order-three
actor lines therefore have disjoint fixed subgroups. If these both have
order four, they complement each other. The final assembly lemma reduces
the intrinsic pair theorem to counting the supporting actor lines.

Source: Stellmacher, *On the 2-local structure of N-groups*, printed p.47,
(9.1)(8), specifically its elementary-nine representation step.
-/

@[expose] public section

open scoped IsMulCommutative

namespace Stellmacher.SectionOne

private theorem elementary_subgroup
    {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (support : Subgroup V) : IsElementaryAbelian 2 support where
  toIsMulCommutative :=
    ⟨⟨fun left right => Subtype.ext (mul_comm (left : V) (right : V))⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro value
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (value : V)

theorem nineCoreSupportDecomposition_common_fixed_eq_bot
    {K V : Type*} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (core : Subgroup K) (hcoreCard : Nat.card core = 9)
    (hVcard : Nat.card V = 16)
    (hfaith : fixingSubgroup K (Set.univ : Set V) = ⊥) :
    FixedPoints.subgroup core V = ⊥ := by
  classical
  let fixed : Subgroup V := FixedPoints.subgroup core V
  let moved : Subgroup V := commutatorAction core V
  have hnotop : fixed ≠ ⊤ := by
    intro htop
    have hbot : core = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro actor hactor
      have hfix : actor ∈ fixingSubgroup K (Set.univ : Set V) := by
        rw [mem_fixingSubgroup_iff]
        intro value _
        have hvalue : value ∈ fixed := htop ▸ Subgroup.mem_top value
        exact hvalue (⟨actor, hactor⟩ : core)
      simpa [hfaith] using hfix
    simp [hbot] at hcoreCard
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hpgroup : IsPGroup 3 core :=
    IsPGroup.of_card (p := 3) (n := 2) (by simpa using hcoreCard)
  have hmod := hpgroup.card_modEq_card_fixedPoints V
  change Nat.ModEq 3 (Nat.card V) (Nat.card fixed) at hmod
  have hdvd : Nat.card fixed ∣ 2 ^ 4 := by
    simpa [hVcard] using fixed.card_subgroup_dvd_card
  have hfixedCard : Nat.card fixed = 1 ∨ Nat.card fixed = 4 := by
    obtain ⟨exponent, hbound, hpower⟩ :=
      (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hdvd
    interval_cases exponent
    · exact Or.inl (by simpa using hpower)
    · rw [hpower, hVcard] at hmod
      norm_num [Nat.ModEq] at hmod
    · exact Or.inr (by simpa using hpower)
    · rw [hpower, hVcard] at hmod
      norm_num [Nat.ModEq] at hmod
    · exact (hnotop (Subgroup.eq_top_of_card_eq _
        (by simpa [hVcard] using hpower))).elim
  rcases hfixedCard with hone | hfour
  · exact (Subgroup.card_eq_one.mp hone)
  have hcompl : IsCompl fixed moved :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun left right => mul_comm left right))
      (by rw [hcoreCard, hVcard]; decide) inferInstance
  have hprod := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint fixed moved
    Subgroup.le_normalizer_of_normal hcompl.disjoint
  rw [hcompl.sup_eq_top, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup V) ≃* V).toEquiv,
    hVcard, hfour] at hprod
  have hmovedCard : Nat.card moved = 4 := by omega
  let _ : IsInvariant core V moved := commutatorAction_isInvariant
  let _ : IsElementaryAbelian 2 moved := elementary_subgroup moved
  have hmovedFaith : fixingSubgroup core (Set.univ : Set moved) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro actor hactor
    rw [mem_fixingSubgroup_iff] at hactor
    have hambient : (actor : K) ∈ fixingSubgroup K (Set.univ : Set V) := by
      rw [mem_fixingSubgroup_iff]
      intro value _
      have hvalue : value ∈ fixed ⊔ moved := by
        rw [hcompl.sup_eq_top]
        exact Subgroup.mem_top value
      obtain ⟨left, hleft, right, hright, rfl⟩ :=
        Subgroup.mem_sup_of_normal_left.mp hvalue
      have hleftFix : (actor : K) • left = left := hleft actor
      have hrightFix : (actor : K) • right = right :=
        congrArg Subtype.val (hactor (⟨right, hright⟩ : moved) (Set.mem_univ _))
      rw [smul_mul', hleftFix, hrightFix]
    apply Subtype.ext
    simpa [hfaith] using hambient
  obtain ⟨embedding, hinjective, _⟩ :=
    FourGroupMatrixCoordinates.faithful_card_four_embedding hmovedFaith hmovedCard
  have hdiv := Subgroup.card_dvd_of_injective embedding hinjective
  obtain ⟨equivalence⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  rw [hcoreCard, Nat.card_congr equivalence.toEquiv, Nat.card_perm, Nat.card_fin] at hdiv
  norm_num at hdiv

theorem nineCoreSupportDecomposition_distinct_lines_sup
    {K : Type*} [Group K] [Finite K]
    (core first second : Subgroup K) (hcoreCard : Nat.card core = 9)
    (hfirst : first ≤ core) (hsecond : second ≤ core)
    (hfirstCard : Nat.card first = 3) (hsecondCard : Nat.card second = 3)
    (hne : first ≠ second) : first ⊔ second = core := by
  have hle : first ⊔ second ≤ core := sup_le hfirst hsecond
  have hdvd : Nat.card (first ⊔ second : Subgroup K) ∣ 3 ^ 2 := by
    simpa [hcoreCard] using Subgroup.card_dvd_of_le hle
  obtain ⟨exponent, hbound, hpower⟩ :=
    (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hdvd
  have hboundFirst := Subgroup.card_le_of_le (show first ≤ first ⊔ second from le_sup_left)
  interval_cases exponent
  · simp [hfirstCard, hpower] at hboundFirst
  · have heqFirst : first = first ⊔ second :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by simp [hfirstCard, hpower])
    have heqSecond : second = first ⊔ second :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by simp [hsecondCard, hpower])
    exact (hne (heqFirst.trans heqSecond.symm)).elim
  · exact Subgroup.eq_of_le_of_card_ge hle (by simp [hcoreCard, hpower])

theorem nineCoreSupportDecomposition_distinct_lines_fixed_isCompl
    {K V : Type*} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (core first second : Subgroup K) (hcoreCard : Nat.card core = 9)
    (hVcard : Nat.card V = 16)
    (hfaith : fixingSubgroup K (Set.univ : Set V) = ⊥)
    (hfirst : first ≤ core) (hsecond : second ≤ core)
    (hfirstCard : Nat.card first = 3) (hsecondCard : Nat.card second = 3)
    (hne : first ≠ second)
    (hfirstFixed : Nat.card (FixedPoints.subgroup first V) = 4)
    (hsecondFixed : Nat.card (FixedPoints.subgroup second V) = 4) :
    IsCompl (FixedPoints.subgroup first V) (FixedPoints.subgroup second V) := by
  have hjoin := nineCoreSupportDecomposition_distinct_lines_sup core first second
    hcoreCard hfirst hsecond hfirstCard hsecondCard hne
  have hfixed := nineCoreSupportDecomposition_common_fixed_eq_bot core hcoreCard hVcard hfaith
  have hdisjoint : Disjoint (FixedPoints.subgroup first V) (FixedPoints.subgroup second V) := by
    rw [disjoint_iff_inf_le]
    intro value hvalue
    have hkernel : first ⊔ second ≤ fixingSubgroup K ({value} : Set V) := by
      apply sup_le
      · intro actor hactor
        rw [mem_fixingSubgroup_iff]
        intro point hpoint
        rcases Set.mem_singleton_iff.mp hpoint with rfl
        exact hvalue.1 (⟨actor, hactor⟩ : first)
      · intro actor hactor
        rw [mem_fixingSubgroup_iff]
        intro point hpoint
        rcases Set.mem_singleton_iff.mp hpoint with rfl
        exact hvalue.2 (⟨actor, hactor⟩ : second)
    have hcommon : value ∈ FixedPoints.subgroup core V := by
      intro actor
      have hactor : (actor : K) ∈ fixingSubgroup K ({value} : Set V) :=
        hkernel (hjoin.symm ▸ actor.property)
      rw [mem_fixingSubgroup_iff] at hactor
      exact hactor value (Set.mem_singleton value)
    simpa [hfixed] using hcommon
  have hcard := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint
    (FixedPoints.subgroup first V) (FixedPoints.subgroup second V)
    Subgroup.le_normalizer_of_normal hdisjoint
  have htop : FixedPoints.subgroup first V ⊔ FixedPoints.subgroup second V = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    simpa only [hfirstFixed, hsecondFixed, hVcard] using hcard
  exact ⟨hdisjoint, codisjoint_iff.mpr htop⟩

theorem nineCoreSupportDecomposition_intrinsic_pair_of_supporting_lines_card
    {K V : Type*} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (core : Subgroup K) (hcoreCard : Nat.card core = 9)
    (hVcard : Nat.card V = 16)
    (hfaith : fixingSubgroup K (Set.univ : Set V) = ⊥)
    (hlines : Nat.card {line : Subgroup K // line ≤ core ∧ Nat.card line = 3 ∧
      Nat.card (FixedPoints.subgroup line V) = 4} = 2) :
    ∃ first second : Subgroup V, IsCompl first second ∧
      ∀ support : Subgroup V,
        NineCoreSupportDecompositionIntrinsic core support ↔
          support = first ∨ support = second := by
  classical
  obtain ⟨first, second, hne, hcover⟩ := Nat.card_eq_two_iff.mp hlines
  have hcompl := nineCoreSupportDecomposition_distinct_lines_fixed_isCompl
    core first.val second.val hcoreCard hVcard hfaith
    first.property.1 second.property.1 first.property.2.1 second.property.2.1
    (fun heq => hne (Subtype.ext heq)) first.property.2.2 second.property.2.2
  refine ⟨FixedPoints.subgroup first.val V, FixedPoints.subgroup second.val V, hcompl, ?_⟩
  intro support
  constructor
  · rintro ⟨hcard, line, hle, hlineCard, rfl⟩
    let supportingLine : {line : Subgroup K // line ≤ core ∧ Nat.card line = 3 ∧
        Nat.card (FixedPoints.subgroup line V) = 4} := ⟨line, hle, hlineCard, hcard⟩
    have hmem : supportingLine ∈ ({first, second} : Set _) :=
      hcover.symm ▸ Set.mem_univ supportingLine
    rcases Set.mem_insert_iff.mp hmem with heq | heq
    · exact Or.inl (congrArg (fun actorLine : Subgroup K => FixedPoints.subgroup actorLine V)
        (congrArg Subtype.val heq))
    · exact Or.inr (congrArg (fun actorLine : Subgroup K => FixedPoints.subgroup actorLine V)
        (congrArg Subtype.val (Set.mem_singleton_iff.mp heq)))
  · rintro (rfl | rfl)
    · exact ⟨first.property.2.2, first.val, first.property.1, first.property.2.1, rfl⟩
    · exact ⟨second.property.2.2, second.val, second.property.1, second.property.2.1, rfl⟩

end Stellmacher.SectionOne
