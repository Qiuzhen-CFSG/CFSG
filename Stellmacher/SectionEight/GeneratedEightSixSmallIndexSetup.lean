module

public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_1
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Stellmacher.ExceptionalType

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u v

public structure EightSixSmallIndexOrderData
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (D Q : Subgroup G) : Prop where
  quotient_card : QuotientCardEq Q D 4
  center_intersection : D ⊓ CenterAmbient Q = ZAt graph path.a
  center_index : QuotientCardEq D (ZAt graph path.a) 1 ∨
    QuotientCardEq D (ZAt graph path.a) 2
  core_eq : Q = QAt graph path.a

public structure EightSixSmallIndexModelData
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (Q : Subgroup G) : Prop where
  next_quotient : QuotientIsModel (GAt graph path.firstStep)
    (QAt graph path.firstStep) SL2Two
  core_model : IsModel (twoCoreIn (EAt graph path.a)) (C4 × C4)
  generated : ∃ actor : G,
    (actor = 1 ∨ IsInvertingOn actor (twoCoreIn (EAt graph path.a))) ∧
    Q = GeneratedWith (twoCoreIn (EAt graph path.a)) actor
  next_core : (IsCentralProductModel (QAt graph path.firstStep) C4 Q8 ∨
    IsCentralProductQ8Q8 (QAt graph path.firstStep)) ∧
    IsModel (QAt graph path.firstStep ⊓ EAt graph path.firstStep) Q8

public theorem eight_six_not_le_of_index_two
    {G : Type u} [Group G] [Finite G] {A D : Subgroup G}
    (hindex : QuotientCardEq A (A ⊓ D) 2) : ¬ A ≤ D := by
  intro hle
  have hpositive : 0 < Nat.card A := Nat.card_pos
  change Nat.card A = 2 * Nat.card (A ⊓ D : Subgroup G) at hindex
  rw [inf_eq_left.mpr hle] at hindex
  omega

public theorem EightSixSmallIndexOrderData.sylow_card
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    {D Q : Subgroup G} (orders : EightSixSmallIndexOrderData graph path D Q)
    (hquot : QuotientIsModel (GAt graph path.a) (QAt graph path.a) SL2Two)
    (hcard : Nat.card (ZAt graph path.a) = 4) :
    Nat.card S = 2 ^ 5 ∨ Nat.card S = 2 ^ 6 := by
  have hQcard : Nat.card Q = 16 ∨ Nat.card Q = 32 := by
    have hratio := orders.quotient_card
    change Nat.card Q = 4 * Nat.card D at hratio
    rcases orders.center_index with hindex | hindex
    · change Nat.card D = 1 * Nat.card (ZAt graph path.a) at hindex
      rw [hcard] at hindex
      left
      omega
    · change Nat.card D = 2 * Nat.card (ZAt graph path.a) at hindex
      rw [hcard] at hindex
      right
      omega
  have hle : Q ≤ GAt graph path.a := by
    rw [orders.core_eq]
    change graph.twoCoreAt path.a ≤ graph.vertexStabilizer path.a
    rw [graph.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  rw [← orders.core_eq] at hquot
  obtain ⟨projection, hsurjective, hkernel⟩ := hquot
  have hlocal := projection.ker.index_mul_card
  rw [Subgroup.index_ker, projection.range_eq_top_of_surjective hsurjective,
    Subgroup.card_top, hkernel,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hlocal
  have hmodelcard : Nat.card SL2Two = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  rw [hmodelcard] at hlocal
  obtain ⟨_, sylow, hsylow⟩ := (SevenSix.edge_sylow_data hyp graph path).1
  have hScard : Nat.card S = Nat.card sylow := by
    conv_lhs => rw [← hsylow]
    exact (Nat.card_congr ((sylow : Subgroup (GAt graph path.a)).equivMapOfInjective
      (GAt graph path.a).subtype (GAt graph path.a).subtype_injective).toEquiv).symm
  rw [hScard, sylow.card_eq_multiplicity, ← hlocal]
  rcases hQcard with hQcard | hQcard
  · left
    rw [hQcard]
    congr 1
    change Nat.factorization (3 * 2 ^ 5) 2 = 5
    rw [Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  · right
    rw [hQcard]
    congr 1
    change Nat.factorization (3 * 2 ^ 6) 2 = 6
    rw [Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]

private theorem quotient_model_map_equiv
    {G : Type u} [Group G] {Model : Type v} [Group Model]
    {A B : Subgroup G} (equiv : G ≃* G)
    (hmodel : QuotientIsModel A B Model) :
    QuotientIsModel (A.map equiv.toMonoidHom) (B.map equiv.toMonoidHom) Model := by
  obtain ⟨projection, hsurjective, hkernel⟩ := hmodel
  let localEquiv := A.equivMapOfInjective equiv.toMonoidHom equiv.injective
  refine ⟨projection.comp localEquiv.symm.toMonoidHom,
    hsurjective.comp localEquiv.symm.surjective, ?_⟩
  ext point
  change projection (localEquiv.symm point) = 1 ↔
    (point : G) ∈ B.map equiv.toMonoidHom
  rw [← MonoidHom.mem_ker, hkernel, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv]
  have hcoe : ((localEquiv.symm point : A) : G) = equiv.symm (point : G) := by
    apply equiv.injective
    rw [equiv.apply_symm_apply]
    exact congrArg Subtype.val (localEquiv.apply_symm_apply point)
  rw [hcoe]

public theorem eight_six_quotient_models_of_critical_edge
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} {Model : Type v} [Group Model]
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hinitial : QuotientIsModel (GAt graph path.a) (QAt graph path.a) Model)
    (hnext : QuotientIsModel (GAt graph path.firstStep)
      (QAt graph path.firstStep) Model) :
    ∀ vertex : graph.Vertex, QuotientIsModel (GAt graph vertex)
      (QAt graph vertex) Model := by
  have hbase : QuotientIsModel P1 (twoCoreIn P1) Model ∧
      QuotientIsModel P2 (twoCoreIn P2) Model := by
    simp only [QAt, q, graph.twoCoreAt_def, GAt] at hinitial hnext
    change QuotientIsModel (stabilizer graph path.a)
      (twoCoreIn (stabilizer graph path.a)) Model at hinitial
    change QuotientIsModel (stabilizer graph path.firstStep)
      (twoCoreIn (stabilizer graph path.firstStep)) Model at hnext
    rcases path.edge_stabilizers_are_P with hedge | hedge
    · exact ⟨by simpa only [hedge.1] using hinitial,
        by simpa only [hedge.2] using hnext⟩
    · exact ⟨by simpa only [hedge.2] using hnext,
        by simpa only [hedge.1] using hinitial⟩
  intro vertex
  obtain ⟨actor, hvertex | hvertex⟩ :=
    (lemma_seven_one hyp graph).vertex_stabilizers_conjugate vertex
  · change QuotientIsModel (graph.stabilizer vertex) (graph.twoCoreAt vertex) Model
    rw [graph.twoCoreAt_def]
    change QuotientIsModel (graph.stabilizer vertex)
      (twoCoreIn (graph.stabilizer vertex)) Model
    rw [hvertex, conjugateBy, SevenSix.twoCoreIn_map_equiv]
    exact quotient_model_map_equiv (MulAut.conj actor) hbase.1
  · change QuotientIsModel (graph.stabilizer vertex) (graph.twoCoreAt vertex) Model
    rw [graph.twoCoreAt_def]
    change QuotientIsModel (graph.stabilizer vertex)
      (twoCoreIn (graph.stabilizer vertex)) Model
    rw [hvertex, conjugateBy, SevenSix.twoCoreIn_map_equiv]
    exact quotient_model_map_equiv (MulAut.conj actor) hbase.2

public theorem eight_six_caseA_of_order_and_models
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q T : Subgroup G)
    (hprev : previous ∈ Later.Neighborhood graph path.a ∧ previous ≠ path.firstStep)
    (hdefs : D = QAt graph previous ⊓ QAt graph path.firstStep ∧
      L = conjugateClosure (QAt graph previous) (GAt graph path.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt graph path.a))
    (hbase : ⁅D, L⁆ = ZAt graph path.a ∧ QuotientIsElementaryAbelian Q D 2 ∧
      IsElementaryAbelianSubgroup 2 D)
    (hquot : QuotientIsModel (GAt graph path.a) (QAt graph path.a) SL2Two)
    (hcard : Nat.card (ZAt graph path.a) = 4)
    (orders : EightSixSmallIndexOrderData graph path D Q)
    (models : EightSixSmallIndexModelData graph path Q) :
    EightSixCaseATypeData graph path previous D L Q T where
  previous_vertex := hprev
  definitions := hdefs
  base := hbase
  card_S := by
    rcases orders.sylow_card hyp graph path hquot hcard with horder | horder <;>
      rw [horder] <;> norm_num
  local_quotients := eight_six_quotient_models_of_critical_edge hyp graph path
    hquot models.next_quotient
  Q_eq := orders.core_eq
  twoCore_model := models.core_model
  generated := models.generated
  next_twoCore := models.next_core

end Stellmacher.SectionEight
