module

public import Stellmacher.SectionEleven.UniquePairJoin
public import Stellmacher.SectionFiveToSeven.CosetGraphConstruction
public import Stellmacher.SectionFiveToSeven.CriticalPathExistence
public import Stellmacher.SectionEight.LemmaEightTwo

/-!
# The unique pair has one of the noncentral models

Under ambient Hypothesis Two with `S ≠ S0`, (5.1)(c) makes the Sylow
omega-center nonnormal in both members of the pair. The actual generated
coset graph therefore has noncentral vertex centers: the defining join
contains the Sylow omega-center, whose centrality would imply normality.
Edge transitivity propagates this to every vertex. By (7.5), commuting
critical endpoint centers would make the terminal center central, so the
actual critical path supplies the nonzero commutator needed in Section Eight.

The generated local adapter retains Hypothesis Two on the original ambient
group. Applying (8.2) to its distinguished first member and transporting along
`subgroupOfEquivOfLe` classifies the original subgroup `P1`, not a quotient.

Source: Stellmacher Section Eleven, unique-maximal reduction to (8.2),
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionEleven

open Later SectionsFiveToSeven CosetGraphContext

universe u

private theorem noncentral_of_nonnormal
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (vertex : Γ.Vertex)
    (hSyl : IsSylowTwoIn S (stabilizer Γ vertex))
    (hnormal : ¬ NormalIn (omegaOneCenter S) (stabilizer Γ vertex)) :
    ¬ z Γ vertex ≤ CenterAmbient (stabilizer Γ vertex) := by
  intro hcentral
  have homega : omegaOneCenter S ≤ z Γ vertex := by
    obtain ⟨_, sylow, hsylow⟩ := hSyl
    rw [z, Γ.zAt_def]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩
  have hle : omegaOneCenter S ≤ stabilizer Γ vertex :=
    (Subgroup.map_subtype_le _).trans hSyl.1
  apply hnormal
  refine ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr ?_⟩
  apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  exact Subgroup.le_centralizer_iff.mpr
    (homega.trans (hcentral.trans (SevenSix.centerAmbient_le_centralizer _)))

private theorem central_act
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (actor : G) (vertex : Γ.Vertex)
    (hcentral : z Γ vertex ≤ CenterAmbient (stabilizer Γ vertex)) :
    z Γ (Γ.act actor vertex) ≤ CenterAmbient (stabilizer Γ (Γ.act actor vertex)) := by
  have hle : z Γ (Γ.act actor vertex) ≤ stabilizer Γ (Γ.act actor vertex) := by
    rw [z_act, stabilizer_act]
    exact Subgroup.map_mono (hcentral.trans (Subgroup.map_subtype_le _))
  have hcomm : ⁅z Γ (Γ.act actor vertex), stabilizer Γ (Γ.act actor vertex)⁆ = ⊥ := by
    rw [z_act, stabilizer_act]
    change ⁅(z Γ vertex).map (MulAut.conj actor⁻¹).toMonoidHom,
      (stabilizer Γ vertex).map (MulAut.conj actor⁻¹).toMonoidHom⁆ = ⊥
    rw [← Subgroup.map_commutator]
    have hzero : ⁅z Γ vertex, stabilizer Γ vertex⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hcentral.trans (SevenSix.centerAmbient_le_centralizer _))
    rw [hzero, Subgroup.map_bot]
  intro element helement
  refine ⟨⟨element, hle helement⟩, ?_, rfl⟩
  change (⟨element, hle helement⟩ : stabilizer Γ (Γ.act actor vertex)) ∈
    Subgroup.center (stabilizer Γ (Γ.act actor vertex))
  rw [Subgroup.mem_center_iff]
  intro other
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm helement)
    other other.property

private theorem all_centers_noncentral
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (hnormal1 : ¬ NormalIn (omegaOneCenter S) P1)
    (hnormal2 : ¬ NormalIn (omegaOneCenter S) P2) :
    ∀ vertex, ¬ z Γ vertex ≤ CenterAmbient (stabilizer Γ vertex) := by
  have hSyl := SevenSix.edge_sylow_data h Γ cp
  have hn : (¬ NormalIn (omegaOneCenter S) (stabilizer Γ cp.a)) ∧
      ¬ NormalIn (omegaOneCenter S) (stabilizer Γ cp.firstStep) := by
    rcases cp.edge_stabilizers_are_P with hedge | hedge
    · simpa only [hedge.1, hedge.2] using And.intro hnormal1 hnormal2
    · simpa only [hedge.1, hedge.2] using And.intro hnormal2 hnormal1
  have hstart := noncentral_of_nonnormal Γ cp.a hSyl.1 hn.1
  have hnext := noncentral_of_nonnormal Γ cp.firstStep hSyl.2 hn.2
  intro vertex hcentral
  obtain ⟨actor, hvertex | hvertex⟩ := Γ.coset₁_surjective vertex
  all_goals
    have hedge : Γ.adjacent (Γ.coset₁ actor) (Γ.coset₂ actor) := by
      rw [Γ.adj_cosets]
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨actor, Set.mem_smul_set.mpr ⟨1, P1.one_mem, by simp⟩,
        Set.mem_smul_set.mpr ⟨1, P2.one_mem, by simp⟩⟩
  · obtain ⟨transporter, htrans | htrans⟩ :=
      (lemma_seven_one h Γ).edge_not_vertex_transitive.1 hedge cp.firstStep_adj
    · apply hstart
      simpa only [htrans.1] using
        central_act Γ transporter (Γ.coset₁ actor) (hvertex ▸ hcentral)
    · apply hnext
      simpa only [htrans.1] using
        central_act Γ transporter (Γ.coset₁ actor) (hvertex ▸ hcentral)
  · obtain ⟨transporter, htrans | htrans⟩ :=
      (lemma_seven_one h Γ).edge_not_vertex_transitive.1 hedge cp.firstStep_adj
    · apply hnext
      simpa only [htrans.2] using
        central_act Γ transporter (Γ.coset₂ actor) (hvertex ▸ hcentral)
    · apply hstart
      simpa only [htrans.2] using
        central_act Γ transporter (Γ.coset₂ actor) (hvertex ▸ hcentral)

/-- The actual unique pair in (5.1)(c) has an S4 or C2 × S4 first member. -/
public theorem unique_pair_model
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hne : S ≠ (S0 : Subgroup H)) :
    IsModel P1 S4 ∨ IsModel P1 (C2 × S4) := by
  classical
  obtain ⟨hseven, hnormal1, hnormal2⟩ := unique_pair_join_hypothesis h hne
  obtain ⟨Γ⟩ := exists_cosetGraphContext _ _ _ hseven.generated
  obtain ⟨cp⟩ := exists_criticalPath hseven Γ
  have hnoncentral := all_centers_noncentral hseven Γ cp hnormal1 hnormal2
  have hcomm : ⁅Γ.z cp.a, Γ.z cp.a'⁆ ≠ ⊥ := by
    intro hzero
    apply hnoncentral cp.a'
    rw [lemma_seven_five_endpoint_center hseven Γ cp hzero]
    exact SevenSix.omegaOneCenter_le_centerAmbient _
  let ctx : GeneratedSectionEightContext H S0 S P1 P2 :=
    { hypothesisTwo := h, sectionSeven := hseven, Γ := Γ,
      criticalPath := cp, commutator_ne := hcomm }
  obtain ⟨vertex, neighbor, _, hvertex, _⟩ :=
    (lemma_seven_one hseven Γ).distinguished_edge
  have hmodel := SectionEight.lemma_eight_two_local ctx.toLocalContext
    (hnoncentral cp.firstStep) vertex
  change IsModel (stabilizer Γ vertex) S4 ∨
    IsModel (stabilizer Γ vertex) (C2 × S4) at hmodel
  rw [hvertex] at hmodel
  change Nonempty (_ ≃* S4) ∨ Nonempty (_ ≃* (C2 × S4)) at hmodel
  rcases hmodel with hleft | hright
  · exact Or.inl (hleft.map fun equiv => (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : P1 ≤ P1 ⊔ P2)).symm.trans equiv)
  · exact Or.inr (hright.map fun equiv => (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : P1 ≤ P1 ⊔ P2)).symm.trans equiv)

end Stellmacher.SectionEleven
