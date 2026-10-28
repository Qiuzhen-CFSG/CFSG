module
public import Stellmacher.SectionEight.EightSixCanonicalStructure
public import Stellmacher.SectionEight.EightSixSelectedOrbitCore

/-!
# The actual minimal actor in the large-index branch of (8.6)

For the graph-local Section Eight context and predecessor core part A with
|A : A intersect D| at least four, choose an element of A outside the next
two-core minimizing its commutator on Vnext/Znext. The theorem produces the
actual E and index-two subgroup A0 from the prescribed-actor (7.8)
configuration, with its geometric neighbor, generation and quotient data.
It also proves that the E-orbit closure of the initial center lies in Qa.

The common structure gives A ≤ Q and Φ(Q) ≤ D. Frattini monotonicity then
provides the exact extraction input Φ(A) ≤ Qnext, while the large index
forces A outside Qnext. The finite minimum and geometric extraction select
the witnesses. The canonical wrapper derives the local data from (8.5);
the local theorem applies on the actual generated graph as well. Their coatom relation and commutator bound satisfy the
proved orbit-core theorem (9). Every selected object is retained for the
later fixed-space calculations, with no classification alternative assumed.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), printed pp.42–43,
assertion (7), the minimal-actor selection, and assertion (9).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_six_large_index_configuration_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup H)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hQ : Q = twoCoreIn L)
    (equation : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup H) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup H)) :
    let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
    ∃ actor : H, ∃ E A0 : Subgroup H,
      actor ∈ A ∧ actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      (∀ other : H, other ∈ A → other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other) ∧
      E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
        GAt ctx.Γ ctx.criticalPath.firstStep ∧
      Nonempty (QuotientDihedralProduct E (QAt ctx.Γ ctx.criticalPath.firstStep) A0) ∧
      Nonempty (SectionNine.NineThreeGeometricData ctx.Γ
        ctx.criticalPath.firstStep ctx.criticalPath.a A E A0 actor) ∧
      conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
        QAt ctx.Γ ctx.criticalPath.a := by
  classical
  let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
  have hAQ : A ≤ Q := by rw [equation.core_generation]; exact le_sup_left.trans le_sup_left
  have htwoQ : IsPGroup 2 Q := by
    rw [hQ]
    exact (pCore_isPGroup (p := 2)).map _
  let : Fact (IsPGroup 2 Q) := ⟨htwoQ⟩
  let : Fact (IsPGroup 2 A) := ⟨htwoQ.to_le hAQ⟩
  have hAprevious : A ≤ QAt ctx.Γ previous :=
    inf_le_left.trans (eight_six_neighborhood_closure_le_core
      ctx.Γ ctx.criticalPath (by omega) previous)
  have hDnext : D ≤ QAt ctx.Γ ctx.criticalPath.firstStep := hD ▸ inf_le_right
  have hnot : ¬ A ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
    intro hnext
    have hAD : A ≤ D := by rw [hD]; exact le_inf hAprevious hnext
    have hpositive : 0 < Nat.card A := Nat.card_pos
    change 4 * Nat.card (A ⊓ D : Subgroup H) ≤ Nat.card A at hlarge
    rw [inf_eq_left.mpr hAD] at hlarge
    omega
  have hphi : SectionsFiveToSeven.frattiniAmbient A ≤
      QAt ctx.Γ ctx.criticalPath.firstStep := by
    apply le_trans ?_ (equation.core_frattini_le.trans hDnext)
    change (frattini A).map A.subtype ≤ (frattini Q).map Q.subtype
    have hmap := frattini_map_le_of_isPGroup (p := 2) (Subgroup.inclusion hAQ)
    calc
      (frattini A).map A.subtype =
          ((frattini A).map (Subgroup.inclusion hAQ)).map Q.subtype := by
        rw [Subgroup.map_map]
        rfl
      _ ≤ (frattini Q).map Q.subtype := Subgroup.map_mono hmap
  obtain ⟨actor,E,A0,ha,hout,hmin,hgen,hmodel,⟨geom⟩⟩ :=
    eight_six_minimal_actor_configuration ctx.sectionSeven ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      ((SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr
        (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj))
      A inf_le_right hnot hphi (eightSixCommutatorCost ctx.Γ ctx.criticalPath)
  refine ⟨actor,E,A0,ha,hout,hmin,hgen,hmodel,⟨geom⟩,?_⟩
  exact eight_six_selected_orbit_closure_le_initial_core ctx hcenter
    hquot hlength hcard previous D hprev hD equation.intersection_normal E A0
    geom.group_le (geom.coatom_eq ▸ inf_le_left) geom.coatom_card
    geom.coatom_commutator hlarge

public theorem eight_six_large_index_configuration
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup H)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup H) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup H)) :
    let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
    ∃ actor : H, ∃ E A0 : Subgroup H,
      actor ∈ A ∧ actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      (∀ other : H, other ∈ A → other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other) ∧
      E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
        GAt ctx.Γ ctx.criticalPath.firstStep ∧
      Nonempty (QuotientDihedralProduct E (QAt ctx.Γ ctx.criticalPath.firstStep) A0) ∧
      Nonempty (SectionNine.NineThreeGeometricData ctx.Γ
        ctx.criticalPath.firstStep ctx.criticalPath.a A E A0 actor) ∧
      conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
        QAt ctx.Γ ctx.criticalPath.a := by
  obtain ⟨equation, _⟩ := eight_six_common_structure ctx hcenter previous hprev D L Q hD hL hQ
  obtain ⟨hquot, hlength⟩ := lemma_eight_five ctx hcenter
  obtain ⟨w, _⟩ := (lemma_eight_one ctx).barred_decomposition
  have hcard := eight_five_center_card_four_of_fixed_normal ctx hcenter w
    (lemma_eight_four ctx hcenter w)
  exact eight_six_large_index_configuration_local ctx.toLocalContext hcenter hquot hlength
    hcard previous D L Q hprev hD hQ equation hlarge

end Stellmacher.SectionEight
