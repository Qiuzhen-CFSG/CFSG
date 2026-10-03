module

public import Stellmacher.SectionEight.GeneratedEightSixEquationOneSetup

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_normal_two_subgroup_le_core
    {G : Type u} [Group G] (D P : Subgroup G)
    (hnormal : NormalIn D P) (htwo : IsPGroup 2 D) :
    D ≤ twoCoreIn P := by
  have hnative : IsPGroup 2 (D.subgroupOf P) :=
    htwo.of_equiv (Subgroup.subgroupOfEquivOfLe hnormal.1).symm
  have hle : D.subgroupOf P ≤ pCore 2 P := le_sSup ⟨hnormal.2, hnative⟩
  calc
    D = (D.subgroupOf P).map P.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hnormal.1).symm
    _ ≤ _ := Subgroup.map_mono hle

public theorem eight_six_two_core_is_two_group
    {G : Type u} [Group G] (P : Subgroup G) :
    IsPGroup 2 (twoCoreIn P) :=
  (pCore_isPGroup (p := 2) (G := P)).map P.subtype

public theorem eight_six_action_core_containments
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex)
    (hprevious : previous ∈ Later.Neighborhood graph path.a)
    (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L)
    (action : EightSixEquationOneActionData graph path D L Q) :
    D ≤ Q ∧ Q ≤ QAt graph path.a ∧ ZAt graph path.a ≤ D := by
  have hclosure := eight_six_previous_closure_containments hyp graph path previous hprevious
  rw [← hL] at hclosure
  have hLnorm : GAt graph path.a ≤ Subgroup.normalizer (L : Set G) := by
    rw [hL]
    exact eight_six_conjugate_closure_normalizer _ _
  have hDnorm : GAt graph path.a ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer action.intersection_normal.1).mp
      action.intersection_normal.2
  have hseed : QAt graph previous ≤ L := by
    rw [hL]
    intro element helement
    apply Subgroup.subset_closure
    exact ⟨1, ⟨element, helement⟩, by simp⟩
  have hDL : D ≤ L := (hD.le.trans inf_le_left).trans hseed
  have hDtwo : IsPGroup 2 D := by
    apply IsPGroup.to_le (K := QAt graph previous) _ (hD.le.trans inf_le_left)
    change IsPGroup 2 (graph.twoCoreAt previous)
    rw [graph.twoCoreAt_def]
    exact eight_six_two_core_is_two_group _
  have hDQ : D ≤ Q := by
    rw [hQ]
    exact eight_six_normal_two_subgroup_le_core D L
      ⟨hDL, Subgroup.normal_subgroupOf_of_le_normalizer (hclosure.1.trans hDnorm)⟩ hDtwo
  have hQnormal : NormalIn Q (GAt graph path.a) := by
    rw [hQ]
    exact ⟨(SevenSix.twoCoreIn_le L).trans hclosure.1,
      SevenSix.twoCoreIn_normal_of_normal L _ hclosure.1
        (Subgroup.normal_subgroupOf_of_le_normalizer hLnorm)⟩
  have hQcore : Q ≤ QAt graph path.a := by
    change Q ≤ graph.twoCoreAt path.a
    rw [graph.twoCoreAt_def]
    exact eight_six_normal_two_subgroup_le_core Q _ hQnormal
      (hQ ▸ eight_six_two_core_is_two_group L)
  refine ⟨hDQ, hQcore, ?_⟩
  rw [← action.residual_commutator]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((SevenSix.twoResidualIn_le L).trans (hclosure.1.trans hDnorm))

public theorem eight_six_frattini_le_of_commutators_and_squares
    {G : Type u} [Group G] [Finite G] (Q D : Subgroup G)
    (htwo : IsPGroup 2 Q) (hcomm : ⁅Q, Q⁆ ≤ D)
    (hsquares : ∀ element ∈ Q, element ^ 2 ∈ D) :
    FrattiniAmbient Q ≤ D := by
  let _ : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  apply Subgroup.map_le_iff_le_comap.mpr
  rw [frattini_eq_closure_commutator_union_powers (p := 2)]
  apply (Subgroup.closure_le _).mpr
  rintro element (hderived | ⟨representative, rfl⟩)
  · have hmapped : (_root_.commutator Q).map Q.subtype = ⁅Q, Q⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator]
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hcomm (hmapped ▸ Subgroup.mem_map.mpr ⟨element, hderived, rfl⟩)
  · exact hsquares representative representative.property

public theorem eight_six_frattini_le_of_three_factor_generation
    {G : Type u} [Group G] [Finite G] (Q A B D : Subgroup G)
    (htwo : IsPGroup 2 Q) (hnormal : (D.subgroupOf Q).Normal)
    (hgen : Q = A ⊔ B ⊔ D) (hcomm : ⁅Q, Q⁆ ≤ D)
    (hAsquare : ∀ element ∈ A, element ^ 2 ∈ D)
    (hBsquare : ∀ element ∈ B, element ^ 2 ∈ D) :
    FrattiniAmbient Q ≤ D := by
  let _ := hnormal
  have hderived : _root_.commutator Q ≤ D.subgroupOf Q := by
    intro element helement
    apply hcomm
    have hmapped : (_root_.commutator Q).map Q.subtype = ⁅Q, Q⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator]
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hmapped ▸ Subgroup.mem_map.mpr ⟨element, helement, rfl⟩
  let _ : IsMulCommutative (Q ⧸ D.subgroupOf Q) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := D.subgroupOf Q)).mpr
      hderived
  let _ : CommGroup (Q ⧸ D.subgroupOf Q) := IsMulCommutative.instCommGroup
  let square : Q →* Q ⧸ D.subgroupOf Q :=
    (powMonoidHom 2).comp (QuotientGroup.mk' (D.subgroupOf Q))
  let kernel : Subgroup G := square.ker.map Q.subtype
  have hkernel (element : G) (helement : element ∈ Q) :
      element ∈ kernel ↔ element ^ 2 ∈ D := by
    have hzero : square ⟨element, helement⟩ = 1 ↔ element ^ 2 ∈ D := by
      change (QuotientGroup.mk' (D.subgroupOf Q) ⟨element, helement⟩) ^ 2 = 1 ↔ _
      rw [← map_pow]
      exact QuotientGroup.eq_one_iff (N := D.subgroupOf Q) (⟨element, helement⟩ ^ 2)
    constructor
    · rintro ⟨representative, hrepresentative, heq⟩
      apply hzero.mp
      have heq' : representative = ⟨element, helement⟩ := Subtype.ext heq
      rwa [← heq']
    · intro hsquare
      exact Subgroup.mem_map.mpr ⟨⟨element, helement⟩, hzero.mpr hsquare, rfl⟩
  have hAQ : A ≤ Q := hgen ▸ le_sup_left.trans le_sup_left
  have hBQ : B ≤ Q := hgen ▸ le_sup_right.trans le_sup_left
  have hDQ : D ≤ Q := hgen ▸ le_sup_right
  have hQkernel : Q ≤ kernel := by
    rw [hgen]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro element helement
      exact (hkernel element (hAQ helement)).mpr (hAsquare element helement)
    · intro element helement
      exact (hkernel element (hBQ helement)).mpr (hBsquare element helement)
    · intro element helement
      exact (hkernel element (hDQ helement)).mpr (D.pow_mem helement 2)
  exact eight_six_frattini_le_of_commutators_and_squares Q D htwo hcomm
    (fun element helement => (hkernel element helement).mp (hQkernel helement))

public theorem eight_six_equation_one_core_of_generation_and_quotient_bounds
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex)
    (hprevious : previous ∈ Later.Neighborhood graph path.a)
    (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L)
    (action : EightSixEquationOneActionData graph path D L Q)
    (hgen : Q = (VAt graph previous ⊓ QAt graph path.a) ⊔
      (VAt graph path.firstStep ⊓ QAt graph path.a) ⊔ D)
    (hcomm : ⁅Q, QAt graph path.firstStep⁆ ⊔ D =
      (VAt graph path.firstStep ⊓ QAt graph path.a) ⊔ D)
    (hderived : ⁅Q, Q⁆ ≤ D)
    (hAsquare : ∀ element ∈ VAt graph previous ⊓ QAt graph path.a,
      element ^ 2 ∈ D)
    (hBsquare : ∀ element ∈ VAt graph path.firstStep ⊓ QAt graph path.a,
      element ^ 2 ∈ D) :
    Q = (VAt graph previous ⊓ QAt graph path.a) ⊔
      (VAt graph path.firstStep ⊓ QAt graph path.a) ⊔ D ∧
    (⁅Q, QAt graph path.firstStep⁆ ⊔ D =
      (VAt graph path.firstStep ⊓ QAt graph path.a) ⊔ D) ∧
    FrattiniAmbient Q ≤ D := by
  have hDQ := (eight_six_action_core_containments hyp graph path previous hprevious
    D L Q hD hL hQ action).1
  have hclosure := eight_six_previous_closure_containments hyp graph path previous hprevious
  rw [← hL] at hclosure
  have hQle : Q ≤ GAt graph path.a :=
    (hQ.le.trans (SevenSix.twoCoreIn_le L)).trans hclosure.1
  have hnormal : (D.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDQ).mpr (hQle.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer action.intersection_normal.1).mp
        action.intersection_normal.2))
  exact ⟨hgen, hcomm, eight_six_frattini_le_of_three_factor_generation Q _ _ D
    (hQ ▸ eight_six_two_core_is_two_group L) hnormal hgen hderived hAsquare hBsquare⟩

end Stellmacher.SectionEight
