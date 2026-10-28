module

public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Theory.Frattini.PGroup

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public structure EightSixEquationOneData
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G) : Prop where
  initial_center_trivial : CenterAmbient (GAt graph path.a) = ⊥
  intersection_normal : NormalIn D (GAt graph path.a)
  closure_le : L ≤ GAt graph path.a
  residual_le : EAt graph path.a ≤ L
  sylow_intersection : L ⊓ S = VAt graph path.firstStep ⊔ Q
  first_commutator : ⁅VAt graph path.firstStep, QAt graph path.firstStep⁆ =
    ZAt graph path.firstStep
  residual_commutator : ⁅D, twoResidualIn L⁆ = ZAt graph path.a
  core_generation : Q = (VAt graph previous ⊓ QAt graph path.a) ⊔
    (VAt graph path.firstStep ⊓ QAt graph path.a) ⊔ D
  core_commutator : ⁅Q, QAt graph path.firstStep⁆ ⊔ D =
    (VAt graph path.firstStep ⊓ QAt graph path.a) ⊔ D
  core_frattini_le : FrattiniAmbient Q ≤ D

public theorem eight_six_exists_previous_vertex
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph) :
    ∃ previous : graph.Vertex,
      previous ∈ Later.Neighborhood graph path.a ∧ previous ≠ path.firstStep := by
  classical
  have hnot : ¬ stabilizer graph path.a ≤ stabilizer graph path.firstStep := by
    intro hle
    have htop : stabilizer graph path.firstStep = ⊤ := by
      rcases path.edge_stabilizers_are_P with hedge | hedge
      · rw [hedge.1, hedge.2] at hle
        rw [hedge.2, ← sup_eq_right.mpr hle]
        exact hyp.generated
      · rw [hedge.1, hedge.2] at hle
        rw [hedge.2, ← sup_eq_left.mpr hle]
        exact hyp.generated
    apply (SevenSix.edge_local_data hyp graph path).2.1.1.2.2.1
    rw [htop, twoCoreIn]
    change (pCore 2 (⊤ : Subgroup G)).map
      (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom = ⊥
    rw [pCore_map_iso, hyp.twoCore_eq_bot]
  obtain ⟨actor, hactor, houtside⟩ := SetLike.not_le_iff_exists.mp hnot
  refine ⟨graph.act actor path.firstStep, ?_, ?_⟩
  · apply (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
    have hfix : graph.act actor path.a = path.a :=
      Set.ext_iff.mp (graph.stabilizer_def path.a) actor |>.mp hactor
    have hadj := adjacent_act graph actor path.firstStep_adj
    rwa [hfix] at hadj
  · intro hfix
    exact houtside (Set.ext_iff.mp (graph.stabilizer_def path.firstStep) actor |>.mpr hfix)

public theorem eight_six_quotient_elementary_of_frattini_le
    {G : Type u} [Group G] [Finite G]
    (Q D : Subgroup G) (hQ : IsPGroup 2 Q)
    (hD : (D.subgroupOf Q).Normal)
    (hfrattini : FrattiniAmbient Q ≤ D) :
    QuotientIsElementaryAbelian Q D 2 := by
  let _ := hD
  let _ : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  have hle : frattini Q ≤ D.subgroupOf Q := by
    intro element helement
    exact hfrattini (Subgroup.mem_map.mpr ⟨element, helement, rfl⟩)
  let witness : QuotientWitness Q D := {
    X := Q ⧸ D.subgroupOf Q
    projection := QuotientGroup.mk' (D.subgroupOf Q)
    surjective := QuotientGroup.mk'_surjective _
    kernel_eq := QuotientGroup.ker_mk' _ }
  refine ⟨witness, ?_⟩
  change IsElementaryAbelian 2 (Q ⧸ D.subgroupOf Q)
  refine {
    toIsMulCommutative :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := D.subgroupOf Q)).2
        ((commutator_le_frattini_of_isPGroup (p := 2)).trans hle)
    exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro element
  refine QuotientGroup.induction_on element ?_
  intro representative
  change (QuotientGroup.mk' (D.subgroupOf Q) representative) ^ 2 = 1
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff (N := D.subgroupOf Q) (representative ^ 2)).mpr
  exact hle (pth_power_mem_frattini_of_isPGroup (p := 2) representative)

public theorem eight_six_base_of_equation_one_and_intersection_frattini
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hcommutator : ⁅D, L⁆ = ZAt graph path.a)
    (hfrattini : FrattiniAmbient D = ⊥) :
    ⁅D, L⁆ = ZAt graph path.a ∧ QuotientIsElementaryAbelian Q D 2 ∧
      IsElementaryAbelianSubgroup 2 D := by
  have hQp : IsPGroup 2 Q := by
    rw [hQ, twoCoreIn]
    exact (pCore_isPGroup (p := 2) (G := L)).map L.subtype
  have hDQ : D ≤ Q := by
    rw [data.core_generation]
    exact le_sup_right
  have hQL : Q ≤ L := hQ ▸ SevenSix.twoCoreIn_le L
  have hnormal : (D.subgroupOf Q).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((hQL.trans data.closure_le).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
          data.intersection_normal.2))
  have hDp : IsPGroup 2 D :=
    hQp.of_injective (Subgroup.inclusion hDQ) (Subgroup.inclusion_injective hDQ)
  let _ : Fact (IsPGroup 2 D) := ⟨hDp⟩
  have hfrattiniNative : frattini D = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp hfrattini
  exact ⟨hcommutator,
    eight_six_quotient_elementary_of_frattini_le Q D hQp hnormal data.core_frattini_le,
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hfrattiniNative⟩

public theorem generated_eight_six_defining_witnesses
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2) :
    ∃ (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H)),
      (previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
        previous ≠ ctx.criticalPath.firstStep) ∧
      (D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
        L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
        Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a)) := by
  obtain ⟨previous, hprevious⟩ :=
    eight_six_exists_previous_vertex ctx.sectionSeven ctx.Γ ctx.criticalPath
  let sylow : Sylow 3 (GAt ctx.Γ ctx.criticalPath.a) := Classical.choice inferInstance
  exact ⟨previous, _, _, _, (sylow : Subgroup _).map (GAt ctx.Γ ctx.criticalPath.a).subtype,
    hprevious, rfl, rfl, rfl, sylow, rfl⟩

end Stellmacher.SectionEight
