module

public import Stellmacher.SectionFiveToSeven.Result7_6.LengthOne
public import Stellmacher.SectionFiveToSeven.Result7_6.LongPath

/-!
# Stellmacher (7.6): the first critical edge

Under Section 7 hypotheses, the core intersection at the first critical edge
is not normal in the next stabilizer. Its residual 2-core lies outside the
initial core, and its local conjugates generate a group containing the
initial residual. A neighbor whose core generates the next stabilizer with
the edge stabilizer cannot contain the intersection. The centralizer of the
initial center likewise fails to generate the next stabilizer.

The length-one and longer-path non-normality arguments are proved separately.
For the residual assertion, containment of its 2-core would force the
forbidden normality; (3.4) then gives the generated containment. Transitivity
and finite-cardinality comparison prove the neighbor assertion. Finally the
edge-centralizer equality of (7.4) makes both factors normalize the forbidden
intersection if their join were the entire stabilizer.

Source: B. Stellmacher, Journal of Algebra 190 (1997), Lemma (7.6),
pp. 35–36; `refs/latex/stellmacher-n-group.tex`. The neighbor assertion keeps
the scan-correct noncontainment in the existing public interface.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext SevenSix

universe u v

public structure LemmaSevenSixConclusion
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ) : Prop where
  core_intersection_not_normal :
    ¬ IsNormalIn (q Γ cp.a ⊓ q Γ cp.firstStep)
      (stabilizer Γ cp.firstStep)
  next_residual_core :
    ¬ twoCoreIn (e Γ cp.firstStep) ≤ q Γ cp.a ∧
      e Γ cp.a ≤ conjugateClosure (twoCoreIn (e Γ cp.firstStep))
        (stabilizer Γ cp.a)
  neighbor_core_noncontainment :
    ∀ m : Γ.Vertex, m ∈ neighborhood Γ cp.firstStep →
      q Γ m ⊔ (stabilizer Γ cp.a ⊓ stabilizer Γ cp.firstStep) =
        stabilizer Γ cp.firstStep →
      ¬ q Γ cp.a ⊓ q Γ cp.firstStep ≤ q Γ m
  centralizer_join_proper :
    (Subgroup.centralizer (z Γ cp.a : Set G) ⊓
        stabilizer Γ cp.firstStep) ⊔
      (stabilizer Γ cp.a ⊓ stabilizer Γ cp.firstStep) ≠
      stabilizer Γ cp.firstStep

private theorem core_intersection_normal_of_residual_core_le
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hRleA : twoCoreIn (e Gamma cp.firstStep) ≤ q Gamma cp.a) :
    IsNormalIn (q Gamma cp.a ⊓ q Gamma cp.firstStep)
      (stabilizer Gamma cp.firstStep) := by
  let A := q Gamma cp.a
  let Q := q Gamma cp.firstStep
  let E := e Gamma cp.firstStep
  let R := twoCoreIn E
  let P := stabilizer Gamma cp.firstStep
  let N := A ⊓ Q
  have hcores := local_cores_le_edge_sylow h Gamma cp
  have hA_le_S : A ≤ S := hcores.1
  have hQ_le_S : Q ≤ S := hcores.2
  have hS_le_Ga : S ≤ stabilizer Gamma cp.a := (edge_sylow_data h Gamma cp).1.1
  have hS_le_P : S ≤ P := (edge_sylow_data h Gamma cp).2.1
  have hS_norm_A : S ≤ Subgroup.normalizer (A : Set G) :=
    hS_le_Ga.trans (stabilizer_le_normalizer_q Gamma cp.a)
  have hS_norm_Q : S ≤ Subgroup.normalizer (Q : Set G) :=
    hS_le_P.trans (stabilizer_le_normalizer_q Gamma cp.firstStep)
  have hS_norm_N : S ≤ Subgroup.normalizer (N : Set G) :=
    (le_inf hS_norm_A hS_norm_Q).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hE_le_P : E ≤ P := by
    dsimp [E, P, CosetGraphContext.e]
    rw [Gamma.twoResidualAt_def]
    exact twoResidualIn_le _
  have hQ_le_P : Q ≤ P := by
    dsimp [Q, P, q]
    rw [Gamma.twoCoreAt_def]
    exact twoCoreIn_le _
  have hP_norm_Q : P ≤ Subgroup.normalizer (Q : Set G) := by
    dsimp [Q, P]
    exact stabilizer_le_normalizer_q Gamma cp.firstStep
  have hcommEQ : ⁅E, Q⁆ ≤ R := by
    dsimp [E, Q, R, CosetGraphContext.e, q]
    rw [Gamma.twoResidualAt_def, Gamma.twoCoreAt_def]
    exact residual_commutator_core_le _
  have hRleQ : R ≤ Q := by
    dsimp [E, Q, R, CosetGraphContext.e, q]
    rw [Gamma.twoResidualAt_def, Gamma.twoCoreAt_def,
      residual_core_eq_inter_core]
    exact inf_le_right
  have hE_norm_N : E ≤ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (Subgroup.commutator_mono le_rfl inf_le_right).trans
      (hcommEQ.trans (le_inf hRleA hRleQ))
  have hEP : E ⊔ S = P := by
    dsimp [E, P, CosetGraphContext.e]
    rw [Gamma.twoResidualAt_def]
    exact twoResidualIn_sup_sylow (edge_sylow_data h Gamma cp).2
  have hNleP : N ≤ P := inf_le_right.trans hQ_le_P
  refine ⟨hNleP, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNleP]
  rw [← hEP]
  exact sup_le hE_norm_N hS_norm_N

private theorem next_residual_core_conclusion
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hnotnormal : ¬ IsNormalIn (q Gamma cp.a ⊓ q Gamma cp.firstStep)
      (stabilizer Gamma cp.firstStep)) :
    ¬ twoCoreIn (e Gamma cp.firstStep) ≤ q Gamma cp.a ∧
      e Gamma cp.a ≤
        conjugateClosure (twoCoreIn (e Gamma cp.firstStep))
          (stabilizer Gamma cp.a) := by
  let Ga := stabilizer Gamma cp.a
  let P := stabilizer Gamma cp.firstStep
  let Ea := e Gamma cp.a
  let E := e Gamma cp.firstStep
  let Q := q Gamma cp.firstStep
  let R := twoCoreIn E
  have hRnotA : ¬ R ≤ q Gamma cp.a := by
    intro hR
    exact hnotnormal (core_intersection_normal_of_residual_core_le
      h Gamma cp hR)
  have hRleQ : R ≤ Q := by
    dsimp [R, E, Q, CosetGraphContext.e, q]
    rw [Gamma.twoResidualAt_def, Gamma.twoCoreAt_def,
      residual_core_eq_inter_core]
    exact inf_le_right
  have hRleS : R ≤ S :=
    hRleQ.trans (local_cores_le_edge_sylow h Gamma cp).2
  have hEleP : E ≤ P := by
    dsimp [E, P, CosetGraphContext.e]
    rw [Gamma.twoResidualAt_def]
    exact twoResidualIn_le _
  have hEnormalP : (E.subgroupOf P).Normal := by
    dsimp [E, P, CosetGraphContext.e]
    rw [Gamma.twoResidualAt_def]
    exact twoResidualIn_normal _
  have hRnormalP : (R.subgroupOf P).Normal :=
    twoCoreIn_normal_of_normal E P hEleP hEnormalP
  have hRleP : R ≤ P := hRleS.trans (edge_sylow_data h Gamma cp).2.1
  have hPnormR : P ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRleP).mp hRnormalP
  have hRnormalS : (R.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hRleS).mpr
    exact (edge_sylow_data h Gamma cp).2.1.trans hPnormR
  have h34 := Stellmacher.SectionThree.lemma_three_four S
    (sectionThreeHypotheses h) Ga
    ((pFamily_iff_pSet (⊤ : Subgroup G) S Ga).mp (edge_local_data h Gamma cp).1.1)
    R ⟨hRleS, hRnormalS⟩ (edge_local_data h Gamma cp).1.2
  have hcomm : ⁅Ea, R⁆ = Ea := by
    rcases h34 with hRle | hcomm
    · apply (hRnotA ?_).elim
      rw [q, Gamma.twoCoreAt_def]
      exact hRle
    · change ⁅twoResidualAmbient Ga, R⁆ = twoResidualAmbient Ga at hcomm
      dsimp [Ea, CosetGraphContext.e]
      rw [Gamma.twoResidualAt_def]
      simpa [Ga, stabilizer, twoResidualIn] using hcomm
  exact ⟨hRnotA, residual_le_conjugateClosure_of_commutator_eq
    Gamma cp hcomm⟩

private theorem centralizer_join_proper_of_core_not_normal
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (hnot : ¬ IsNormalIn (q Γ cp.a ⊓ q Γ cp.firstStep)
      (stabilizer Γ cp.firstStep))
    (hedge : S ⊓ Subgroup.centralizer (z Γ cp.a : Set G) = q Γ cp.a) :
    (Subgroup.centralizer (z Γ cp.a : Set G) ⊓
        stabilizer Γ cp.firstStep) ⊔
      (stabilizer Γ cp.a ⊓ stabilizer Γ cp.firstStep) ≠
      stabilizer Γ cp.firstStep := by
  let A := q Γ cp.a
  let B := q Γ cp.firstStep
  let Ga := stabilizer Γ cp.a
  let Gb := stabilizer Γ cp.firstStep
  let C := Subgroup.centralizer (z Γ cp.a : Set G) ⊓ Gb
  let I := Ga ⊓ Gb
  let N := A ⊓ B
  have hcores := local_cores_le_edge_sylow h Γ cp
  have hA_le_S : A ≤ S := hcores.1
  have hB_le_S : B ≤ S := hcores.2
  have hA_le_Ga : A ≤ Ga := by
    dsimp [A, Ga, q, stabilizer]
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hB_le_Gb : B ≤ Gb := by
    dsimp [B, Gb, q, stabilizer]
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hA_normal_Ga : (A.subgroupOf Ga).Normal := by
    dsimp [A, Ga, q, stabilizer]
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_normal _
  have hB_normal_Gb : (B.subgroupOf Gb).Normal := by
    dsimp [B, Gb, q, stabilizer]
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_normal _
  have hGa_normalizes_A : Ga ≤ Subgroup.normalizer A :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA_le_Ga).mp hA_normal_Ga
  have hGb_normalizes_B : Gb ≤ Subgroup.normalizer B :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hB_le_Gb).mp hB_normal_Gb
  have hN_eq : N = B ⊓ C := by
    ext x
    constructor
    · intro hx
      have hxA : x ∈ A := hx.1
      have hxB : x ∈ B := hx.2
      have hxSC : x ∈ S ⊓ Subgroup.centralizer (z Γ cp.a : Set G) := by
        rw [hedge]
        exact hxA
      exact ⟨hxB, hxSC.2, hB_le_Gb hxB⟩
    · intro hx
      have hxB : x ∈ B := hx.1
      have hxA : x ∈ A := by
        change x ∈ q Γ cp.a
        rw [← hedge]
        exact ⟨hB_le_S hxB, hx.2.1⟩
      exact ⟨hxA, hxB⟩
  have hC_normalizes_N : C ≤ Subgroup.normalizer N := by
    rw [hN_eq]
    exact (le_inf (inf_le_right.trans hGb_normalizes_B)
      Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hI_normalizes_N : I ≤ Subgroup.normalizer N := by
    exact (le_inf (inf_le_left.trans hGa_normalizes_A)
      (inf_le_right.trans hGb_normalizes_B)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  intro hjoin
  apply hnot
  change IsNormalIn N Gb
  change C ⊔ I = Gb at hjoin
  have hN_le_Gb : N ≤ Gb := inf_le_right.trans hB_le_Gb
  refine ⟨hN_le_Gb, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN_le_Gb]
  rw [← hjoin]
  exact sup_le hC_normalizes_N hI_normalizes_N

private theorem lemma_seven_six_complete
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    (¬ IsNormalIn (q Gamma cp.a ⊓ q Gamma cp.firstStep)
        (stabilizer Gamma cp.firstStep)) ∧
      (¬ twoCoreIn (e Gamma cp.firstStep) ≤ q Gamma cp.a ∧
        e Gamma cp.a ≤ conjugateClosure (twoCoreIn (e Gamma cp.firstStep))
          (stabilizer Gamma cp.a)) ∧
      (∀ m : Gamma.Vertex, m ∈ neighborhood Gamma cp.firstStep →
        q Gamma m ⊔ (stabilizer Gamma cp.a ⊓
          stabilizer Gamma cp.firstStep) = stabilizer Gamma cp.firstStep →
        ¬ q Gamma cp.a ⊓ q Gamma cp.firstStep ≤ q Gamma m) ∧
      (Subgroup.centralizer (z Gamma cp.a : Set G) ⊓
          stabilizer Gamma cp.firstStep) ⊔
        (stabilizer Gamma cp.a ⊓ stabilizer Gamma cp.firstStep) ≠
          stabilizer Gamma cp.firstStep := by
  have hnotnormal : ¬ IsNormalIn
      (q Gamma cp.a ⊓ q Gamma cp.firstStep)
      (stabilizer Gamma cp.firstStep) := by
    by_cases hlen : cp.length = 1
    · have haMem : cp.firstStep ∈ neighborhood Gamma cp.a :=
        (mem_neighborhood_iff_adjacent Gamma).2 cp.firstStep_adj
      have hZaA : z Gamma cp.a ≤ q Gamma cp.a :=
        ((lemma_seven_three h Gamma).center_core cp.a cp.firstStep haMem).trans
          ((omegaOneCenter_le_centerAmbient (q Gamma cp.a)).trans
            (Subgroup.map_subtype_le (Subgroup.center (q Gamma cp.a))))
      have hZaS : z Gamma cp.a ≤ S :=
        hZaA.trans (local_cores_le_edge_sylow h Gamma cp).1
      have hSleGa : S ≤ stabilizer Gamma cp.a :=
        (edge_sylow_data h Gamma cp).1.1
      have hZaNormalS : ((z Gamma cp.a).subgroupOf S).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZaS]
        exact hSleGa.trans (stabilizer_le_normalizer_z Gamma cp.a)
      exact core_intersection_not_normal_of_length_one
        h Gamma cp hlen hZaNormalS
    · have hlen' : 1 < cp.length := by
        have hpos := cp.length_pos
        omega
      exact core_intersection_not_normal_of_length_gt_one
        h Gamma cp hlen'
  refine ⟨hnotnormal, next_residual_core_conclusion h Gamma cp hnotnormal,
    ?_, ?_⟩
  · intro m hm hgen hle
    exact hnotnormal (core_intersection_normal_of_neighbor_containment
      h Gamma cp m hm hgen hle)
  · exact centralizer_join_proper_of_core_not_normal h Gamma cp hnotnormal
      (lemma_seven_four h Gamma cp).edge_centralizer

/-- **Stellmacher (7.6).**  The four non-normality and containment properties
along the first edge of a critical path. -/
public theorem lemma_seven_six
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ) :
    LemmaSevenSixConclusion Γ cp := by
  obtain ⟨ha, hb, hc, hd⟩ := lemma_seven_six_complete h Γ cp
  exact ⟨ha, hb, hc, hd⟩

end Stellmacher.SectionsFiveToSeven
