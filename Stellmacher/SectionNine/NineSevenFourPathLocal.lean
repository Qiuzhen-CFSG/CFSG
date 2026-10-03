module

public import Stellmacher.SectionNine.CubicCoreIntersection
public import Stellmacher.SectionNine.GeneratedContext

/-!
# Four-path transitivity using only the Section Nine local context

This is a disjoint generalization of `NineSevenFourPathTransitivity`.
The proof uses the genuine Section Seven hypotheses on the graph group,
not Hypothesis Two on that group. The first-step quotient and the quotients
on the initial orbit suffice; no distance-five or order-eight premise is
needed for this local helper.

Source: Stellmacher (9.7), printed p.54/PDF p.44. This proves the four-path
paragraph, not the subsequent Goldschmidt commutator contradiction.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

variable {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}

private theorem mem_stabilizer_iff (Γ : CosetGraphContext G S P1 P2)
    (actor : G) (vertex : Γ.Vertex) :
    actor ∈ stabilizer Γ vertex ↔ Γ.act actor vertex = vertex := by
  exact Set.ext_iff.mp (Γ.stabilizer_def vertex) actor

private theorem act_injective (Γ : CosetGraphContext G S P1 P2) (actor : G) :
    Function.Injective (Γ.act actor) := by
  intro left right heq
  have hinv := congrArg (Γ.act actor⁻¹) heq
  simpa only [← Γ.act_mul, mul_inv_cancel, Γ.act_one] using hinv

private theorem core_le_self (Γ : CosetGraphContext G S P1 P2)
    (vertex : Γ.Vertex) : q Γ vertex ≤ stabilizer Γ vertex := by
  rw [q, Γ.twoCoreAt_def]
  exact SevenSix.twoCoreIn_le _

private theorem core_le_neighbor
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) {vertex neighbor : Γ.Vertex}
    (hadj : Γ.adjacent vertex neighbor) :
    q Γ vertex ≤ stabilizer Γ neighbor := by
  exact ((lemma_seven_three h7 Γ).sylow_and_core vertex neighbor
    ((SevenSix.mem_neighborhood_iff_adjacent Γ).2 hadj) default).2.2

private theorem quotient_model_act
    (Γ : CosetGraphContext G S P1 P2) (actor : G) (vertex : Γ.Vertex)
    (hmodel : QuotientIsModel (GAt Γ vertex) (QAt Γ vertex) SL2Two) :
    QuotientIsModel (GAt Γ (Γ.act actor vertex)) (QAt Γ (Γ.act actor vertex)) SL2Two := by
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  change QuotientIsModel (stabilizer Γ (Γ.act actor vertex))
    (q Γ (Γ.act actor vertex)) SL2Two
  rw [stabilizer_act, SevenSix.q_act]
  let equiv := (GAt Γ vertex).equivMapOfInjective
    (MulAut.conj actor⁻¹).toMonoidHom (MulAut.conj actor⁻¹).injective
  refine ⟨projection.comp equiv.symm.toMonoidHom,
    hsurj.comp equiv.symm.surjective, ?_⟩
  ext point
  change projection (equiv.symm point) = 1 ↔
    (point : G) ∈ (QAt Γ vertex).map (MulAut.conj actor⁻¹).toMonoidHom
  rw [← MonoidHom.mem_ker, hker, Subgroup.mem_map_equiv]
  have heq : (equiv.symm point : G) = (MulAut.conj actor⁻¹).symm (point : G) := by
    apply (MulAut.conj actor⁻¹).injective
    change (equiv (equiv.symm point) : G) = _
    simp only [MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val (equiv.apply_symm_apply point)
  change (equiv.symm point : G) ∈ QAt Γ vertex ↔ _
  rw [heq]

private theorem vertex_in_distinguished_orbits
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (vertex : Γ.Vertex) :
    IsConjugateVertex Γ cp.a vertex ∨ IsConjugateVertex Γ cp.firstStep vertex := by
  have hexists : ∃ neighbor, Γ.adjacent vertex neighbor := by
    obtain ⟨actor, hvertex | hvertex⟩ := Γ.coset₁_surjective vertex
    all_goals
      have hedge : Γ.adjacent (Γ.coset₁ actor) (Γ.coset₂ actor) := by
        rw [Γ.adj_cosets]
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨actor, Set.mem_smul_set.mpr ⟨1, P1.one_mem, by simp⟩,
          Set.mem_smul_set.mpr ⟨1, P2.one_mem, by simp⟩⟩
    · exact ⟨Γ.coset₂ actor, hvertex ▸ hedge⟩
    · exact ⟨Γ.coset₁ actor, hvertex ▸ Γ.adjacent_symm hedge⟩
  obtain ⟨neighbor, hadj⟩ := hexists
  obtain ⟨actor, horiented | hreversed⟩ :=
    (lemma_seven_one h7 Γ).edge_not_vertex_transitive.1 cp.firstStep_adj hadj
  · exact Or.inl ⟨actor, horiented.1⟩
  · exact Or.inr ⟨actor, hreversed.2⟩

private theorem all_vertex_quotients
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (hfirst : QuotientIsModel (GAt Γ cp.firstStep) (QAt Γ cp.firstStep) SL2Two)
    (hstart : ∀ vertex, IsConjugateVertex Γ cp.a vertex →
      QuotientIsModel (GAt Γ vertex) (QAt Γ vertex) SL2Two) :
    ∀ vertex, QuotientIsModel (GAt Γ vertex) (QAt Γ vertex) SL2Two := by
  intro vertex
  rcases vertex_in_distinguished_orbits h7 Γ cp vertex with hleft | ⟨actor, rfl⟩
  · exact hstart vertex hleft
  · exact quotient_model_act Γ actor cp.firstStep hfirst

private theorem four_path_normalize_of_prefix_actions
    (Γ : CosetGraphContext G S P1 P2) (reference : Fin 5 → Γ.Vertex)
    (hextend : ∀ step : Fin 4, ∀ candidate : Γ.Vertex,
      Γ.adjacent (reference step.castSucc) candidate →
      (∀ prior : Fin 3, prior.val + 1 = step.val →
        reference prior.castSucc.castSucc ≠ candidate) →
      ∃ actor : G,
        (∀ index : Fin 5, index.val ≤ step.val →
          Γ.act actor (reference index) = reference index) ∧
        Γ.act actor candidate = reference step.succ)
    (first : Fin 5 → Γ.Vertex) (hstart : first 0 = reference 0)
    (hadj : ∀ index : Fin 4,
      Γ.adjacent (first index.castSucc) (first index.succ))
    (hback : ∀ index : Fin 3,
      first index.castSucc.castSucc ≠ first index.succ.succ) :
    ∃ actor : stabilizer Γ (reference 0),
      ∀ index : Fin 5, Γ.act (actor : G) (first index) = reference index := by
  have hprefix : ∀ bound : ℕ, bound ≤ 4 →
      ∃ actor : stabilizer Γ (reference 0),
        ∀ index : Fin 5, index.val ≤ bound →
          Γ.act (actor : G) (first index) = reference index := by
    intro bound
    induction bound with
    | zero =>
      intro _
      refine ⟨1, ?_⟩
      intro index hindex
      have hzero : index = 0 := Fin.ext (by simpa using hindex)
      subst index
      simpa only [OneMemClass.coe_one, Γ.act_one] using hstart
    | succ bound ih =>
      intro hbound
      obtain ⟨old, hold⟩ := ih (by omega)
      let step : Fin 4 := ⟨bound, by omega⟩
      have hstepadj : Γ.adjacent (reference step.castSucc)
          (Γ.act (old : G) (first step.succ)) := by
        have htransport := adjacent_act Γ (old : G) (hadj step)
        rwa [hold step.castSucc (by rfl)] at htransport
      have hstepback : ∀ prior : Fin 3, prior.val + 1 = step.val →
          reference prior.castSucc.castSucc ≠
            Γ.act (old : G) (first step.succ) := by
        intro prior hprior heq
        have hle : prior.castSucc.castSucc.val ≤ bound := by
          change prior.val ≤ bound
          change prior.val + 1 = bound at hprior
          omega
        rw [← hold prior.castSucc.castSucc hle] at heq
        have hind : prior.succ.succ = step.succ := Fin.ext (by
          change prior.val + 1 + 1 = step.val + 1
          omega)
        exact hback prior (by rw [hind]; exact act_injective Γ (old : G) heq)
      obtain ⟨mover, hfix, hmove⟩ := hextend step _ hstepadj hstepback
      have hmover : mover ∈ stabilizer Γ (reference 0) :=
        (mem_stabilizer_iff Γ mover _).2 (hfix 0 (by simp))
      refine ⟨old * ⟨mover, hmover⟩, ?_⟩
      intro index hindex
      change Γ.act ((old : G) * mover) (first index) = reference index
      rw [Γ.act_mul]
      by_cases hle : index.val ≤ bound
      · rw [hold index hle]
        exact hfix index hle
      · have hind : index = step.succ := Fin.ext (by
          change index.val = bound + 1
          omega)
        subst index
        exact hmove
  obtain ⟨actor, hactor⟩ := hprefix 4 (by rfl)
  exact ⟨actor, fun index => hactor index (by omega)⟩

private theorem four_path_prefix_actions_of_three_local_actions
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (reference : Fin 5 → Γ.Vertex)
    (hadj : ∀ index : Fin 4,
      Γ.adjacent (reference index.castSucc) (reference index.succ))
    (hback : ∀ index : Fin 3,
      reference index.castSucc.castSucc ≠ reference index.succ.succ)
    (hsecond : IsActionTransitiveOn Γ
      (stabilizer Γ (reference 0) ⊓ stabilizer Γ (reference 1))
      (neighborhood Γ (reference 1) \ {reference 0}))
    (hthird : IsActionTransitiveOn Γ (q Γ (reference 1))
      (neighborhood Γ (reference 2) \ {reference 1}))
    (hfourth : IsActionTransitiveOn Γ (q Γ (reference 1) ⊓ q Γ (reference 2))
      (neighborhood Γ (reference 3) \ {reference 2})) :
    ∀ step : Fin 4, ∀ candidate : Γ.Vertex,
      Γ.adjacent (reference step.castSucc) candidate →
      (∀ prior : Fin 3, prior.val + 1 = step.val →
        reference prior.castSucc.castSucc ≠ candidate) →
      ∃ actor : G,
        (∀ index : Fin 5, index.val ≤ step.val →
          Γ.act actor (reference index) = reference index) ∧
        Γ.act actor candidate = reference step.succ := by
  intro step candidate hcand hprior
  have hfix : ∀ vertex : Γ.Vertex, ∀ actor : stabilizer Γ vertex,
      Γ.act (actor : G) vertex = vertex := fun vertex actor =>
    (mem_stabilizer_iff Γ _ vertex).1 actor.property
  have hqfix : ∀ vertex neighbor : Γ.Vertex, Γ.adjacent vertex neighbor →
      ∀ actor : q Γ vertex, Γ.act (actor : G) neighbor = neighbor := by
    intro vertex neighbor hedge actor
    exact (mem_stabilizer_iff Γ _ neighbor).1
      (core_le_neighbor h7 Γ hedge actor.property)
  fin_cases step
  · obtain ⟨actor, hactor⟩ := (lemma_seven_one h7 Γ).local_transitivity (reference 0)
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).2 hcand)
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).2 (hadj 0))
    refine ⟨actor, ?_, hactor⟩
    intro index hindex
    have hzero : index = 0 := Fin.ext (by simpa using hindex)
    subst index
    exact hfix _ actor
  · obtain ⟨actor, hactor⟩ := hsecond
      ⟨(SevenSix.mem_neighborhood_iff_adjacent Γ).2 hcand,
        fun heq => hprior 0 rfl heq.symm⟩
      ⟨(SevenSix.mem_neighborhood_iff_adjacent Γ).2 (hadj 1),
        fun heq => hback 0 heq.symm⟩
    refine ⟨actor, ?_, hactor⟩
    intro index hindex
    have hmem := actor.property
    fin_cases index
    · exact (mem_stabilizer_iff Γ _ _).1 hmem.1
    · exact (mem_stabilizer_iff Γ _ _).1 hmem.2
    all_goals norm_num at hindex
  · obtain ⟨actor, hactor⟩ := hthird
      ⟨(SevenSix.mem_neighborhood_iff_adjacent Γ).2 hcand,
        fun heq => hprior 1 rfl heq.symm⟩
      ⟨(SevenSix.mem_neighborhood_iff_adjacent Γ).2 (hadj 2),
        fun heq => hback 1 heq.symm⟩
    refine ⟨actor, ?_, hactor⟩
    intro index hindex
    fin_cases index
    · exact hqfix _ _ (Γ.adjacent_symm (hadj 0)) actor
    · exact (mem_stabilizer_iff Γ _ _).1 (core_le_self Γ _ actor.property)
    · exact hqfix _ _ (hadj 1) actor
    all_goals norm_num at hindex
  · obtain ⟨actor, hactor⟩ := hfourth
      ⟨(SevenSix.mem_neighborhood_iff_adjacent Γ).2 hcand,
        fun heq => hprior 2 rfl heq.symm⟩
      ⟨(SevenSix.mem_neighborhood_iff_adjacent Γ).2 (hadj 3),
        fun heq => hback 2 heq.symm⟩
    refine ⟨actor, ?_, hactor⟩
    intro index hindex
    have hmem := actor.property
    fin_cases index
    · exact hqfix _ _ (Γ.adjacent_symm (hadj 0)) ⟨actor, hmem.1⟩
    · exact (mem_stabilizer_iff Γ _ _).1 (core_le_self Γ _ hmem.1)
    · exact (mem_stabilizer_iff Γ _ _).1 (core_le_self Γ _ hmem.2)
    · exact hqfix _ _ (hadj 2) ⟨actor, hmem.2⟩
    · norm_num at hindex

private theorem three_local_actions
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (hmodels : ∀ vertex, QuotientIsModel (GAt Γ vertex) (QAt Γ vertex) SL2Two)
    (reference : Fin 5 → Γ.Vertex) (hstart : reference 0 = cp.firstStep)
    (hadj : ∀ index : Fin 4,
      Γ.adjacent (reference index.castSucc) (reference index.succ))
    (hback : ∀ index : Fin 3,
      reference index.castSucc.castSucc ≠ reference index.succ.succ) :
    IsActionTransitiveOn Γ
      (GAt Γ (reference 0) ⊓ GAt Γ (reference 1))
      (neighborhood Γ (reference 1) \ {reference 0}) ∧
    IsActionTransitiveOn Γ (QAt Γ (reference 1))
      (neighborhood Γ (reference 2) \ {reference 1}) ∧
    IsActionTransitiveOn Γ (QAt Γ (reference 1) ⊓ QAt Γ (reference 2))
      (neighborhood Γ (reference 3) \ {reference 2}) := by
  have hlocal := fun vertex => cubic_local_action_of_sl2Two_quotient Γ h7 vertex
    (hmodels vertex)
  have horbit : IsConjugateVertex Γ cp.firstStep (reference 2) := by
    obtain ⟨actor, hactor⟩ := (lemma_seven_one h7 Γ).local_transitivity (reference 1)
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).2 (Γ.adjacent_symm (hadj 0)))
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).2 (hadj 1))
    change Γ.act (actor : G) (reference 0) = reference 2 at hactor
    exact ⟨actor, by simpa only [hstart] using hactor⟩
  refine ⟨?_, ?_, ?_⟩
  · apply (hlocal (reference 1)).punctured_transitivity (reference 0)
      (Γ.adjacent_symm (hadj 0)) _ (by rw [inf_comm])
    rw [inf_comm]
    exact edge_stabilizer_outside_core h7 Γ (Γ.adjacent_symm (hadj 0))
      (hmodels (reference 1))
  · apply (hlocal (reference 2)).punctured_transitivity (reference 1)
      (Γ.adjacent_symm (hadj 1)) _
      (le_inf (core_le_neighbor h7 Γ (hadj 1)) (core_le_self Γ _))
    exact adjacent_cores_incomparable h7 Γ cp hmodels (hadj 1)
  · apply (hlocal (reference 3)).punctured_transitivity (reference 2)
      (Γ.adjacent_symm (hadj 2)) _
      (le_inf (inf_le_right.trans (core_le_neighbor h7 Γ (hadj 2)))
        (inf_le_right.trans (core_le_self Γ _)))
    exact cubic_core_intersection_noncontainment h7 Γ cp hmodels horbit
      (Γ.adjacent_symm (hadj 1)) (hadj 2) (hback 1)

public theorem nineSeven_cubic_four_path_transitivity_local
    (ctx : SectionNineLocalContext G S P1 P2)
    (hfirstModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hstartModels : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two) :
    (∀ vertex, Nat.card {neighbor // ctx.Γ.adjacent vertex neighbor} = 3) ∧
      ∀ first second : Fin 5 → ctx.Γ.Vertex,
        first 0 = ctx.criticalPath.firstStep →
        second 0 = ctx.criticalPath.firstStep →
        (∀ index : Fin 4,
          ctx.Γ.adjacent (first index.castSucc) (first index.succ)) →
        (∀ index : Fin 4,
          ctx.Γ.adjacent (second index.castSucc) (second index.succ)) →
        (∀ index : Fin 3, first index.castSucc.castSucc ≠ first index.succ.succ) →
        (∀ index : Fin 3, second index.castSucc.castSucc ≠ second index.succ.succ) →
        ∃ actor : GAt ctx.Γ ctx.criticalPath.firstStep,
          ∀ index : Fin 5, ctx.Γ.act (actor : G) (first index) = second index := by
  have h7 := ctx.sectionSeven
  have hmodels := all_vertex_quotients h7 ctx.Γ ctx.criticalPath hfirstModel hstartModels
  refine ⟨fun vertex => (cubic_local_action_of_sl2Two_quotient ctx.Γ h7 vertex
    (hmodels vertex)).degree, ?_⟩
  intro first second hfirst hsecond hfirstadj hsecondadj hfirstback hsecondback
  obtain ⟨hsecondAction, hthirdAction, hfourthAction⟩ := three_local_actions
    h7 ctx.Γ ctx.criticalPath hmodels second hsecond hsecondadj hsecondback
  have hextend := four_path_prefix_actions_of_three_local_actions
    h7 ctx.Γ second hsecondadj hsecondback hsecondAction hthirdAction hfourthAction
  obtain ⟨actor, hactor⟩ := four_path_normalize_of_prefix_actions ctx.Γ second hextend
    first (hfirst.trans hsecond.symm) hfirstadj hfirstback
  refine ⟨⟨actor, ?_⟩, hactor⟩
  simpa only [hsecond] using actor.property

end Stellmacher.SectionNine
