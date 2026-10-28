module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceComplete
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.OddCore
public import Theory.GroupTheory.GeneralizedFitting.NoComponentInverter

/-!
# Nontrivial action at a maximal escaping subspace

For a maximal member U of the actual obstruction family with corank greater
than one, the odd core of H = C_G(U) vanishes. If H has no component, it has
characteristic two, and the source E.6.7 product supplies an escaping block.
Otherwise the source E.6.8 alternatives apply to an actual component of H.

Maximality identifies U with C_V(L) in both branches. Alternating blocks and
the corank-one component rows are impossible; the alternating and symplectic
Borel escape rows contradict maximality directly. The remaining source
decompositions V = U[V,X] force a moving element of M ∩ C_G(U). For ordinary
components X = L ∩ M suffices, so no cyclic complement or regularity theorem
is needed for this consequence. All earlier inputs are supplied by their
known-simple source proofs, retaining the literal relative components and
odd-index residual in the obstruction family.

Source: Aschbacher--Smith E.6.11(2), printed pp.249--250, using E.6.7--9,
in `refs/quasithin.pdf`. Only the moving-element conclusion is asserted.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06
open Components InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- The initial structural dichotomy of E.6.11 under maximal escape. -/
theorem component_or_characteristicTwo_of_maximal_escape
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hmax : ∀ W : Subgroup G, U < W → W ≤ V → centralizer (W : Set G) ≤ M)
    (hn : 1 < subgroupCorank V U) :
    (∃ L : Subgroup G, ComponentIn (centralizer (U : Set G)) L) ∨
      HasCharacteristicTwo (centralizer (U : Set G)) := by
  let H := centralizer (U : Set G)
  by_cases hc : ∃ L : Subgroup G, ComponentIn H L
  · exact Or.inl hc
  right
  have ho := h.oddCore_eq_bot_of_maximal_escape (source_earlierLocalFacts h) hU hmax hn
  have hnc : ∀ J : Subgroup H, ¬ IsComponent H J := by
    intro J hJ
    apply hc
    refine ⟨J.map H.subtype, map_subtype_le J, ?_⟩
    have he : (J.map H.subtype).subgroupOf H = J :=
      comap_map_eq_self_of_injective H.subtype_injective J
    rwa [he]
  have hh := centralizer_core_product_le_of_no_components 2 hnc
  change pPrimeCore 2 H = ⊥ at ho
  change HasCharacteristicTwo H
  simpa only [HasCharacteristicTwo, ho, sup_bot_eq] using hh

/-- The original E.6.7 block product supplies movement in characteristic two. -/
theorem action_escape_of_characteristicTwo
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hU : U ∈ obstructionFamily M V)
    (hmax : ∀ W : Subgroup G, U < W → W ≤ V → centralizer (W : Set G) ≤ M)
    (hn : 1 < subgroupCorank V U)
    (hc : HasCharacteristicTwo (centralizer (U : Set G))) :
    ∃ x ∈ M ⊓ centralizer (U : Set G), x ∉ centralizer (V : Set G) := by
  obtain ⟨d⟩ := e67Input_knownSimple h U hU (centralizer (U : Set G))
    (inf_le_right.trans (Subgroup.centralizer_le hU.1)) le_rfl hc
  have hex : ∃ i, ¬ d.block i ≤ M := by
    by_contra! hall
    exact hU.2.2.1 (d.generated.le.trans (sup_le inf_le_right (iSup_le hall)))
  obtain ⟨i, hi⟩ := hex
  have hfixed : V ⊓ centralizer (d.block i : Set G) = U :=
    (fixedSpace_eq_of_maximal_escape hU.1 hmax (d.le i) hi).symm
  have ha (n : ℕ) : ¬ ChapterC.IsAlternatingBlock (d.block i) n := by
    intro ht
    have he := (d.alternating i n ht).1
    rw [hfixed] at he
    omega
  obtain ⟨n, ht⟩ : ∃ n, ChapterC.IsL2EvenBlock (d.block i) n := by
    rcases d.type i with ht | ht | ht
    · exact ht
    · exact (ha 3 ht).elim
    · exact (ha 5 ht).elim
  obtain ⟨X, hX, _, _, hgen, _⟩ := d.rankOne i n ht
  have hXC : X ≤ M ⊓ centralizer (U : Set G) :=
    le_inf (hX.trans inf_le_right) ((hX.trans inf_le_left).trans (d.le i))
  rw [hfixed] at hgen
  exact (h.action_escape_of_decomposition hU hn hXC hgen).2

/-- The original E.6.8 component alternatives supply movement at maximal escape. -/
theorem action_escape_of_component
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hU : U ∈ obstructionFamily M V)
    (hmax : ∀ W : Subgroup G, U < W → W ≤ V → centralizer (W : Set G) ≤ M)
    (hn : 1 < subgroupCorank V U)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    ∃ x ∈ M ⊓ centralizer (U : Set G), x ∉ centralizer (V : Set G) := by
  have hfixed : V ⊓ centralizer (L : Set G) = U :=
    (fixedSpace_eq_of_maximal_escape hU.1 hmax hL.1
      (component_not_le h (source_earlierLocalFacts h) hU hL)).symm
  have hcor : actionCorank V L = subgroupCorank V U := by rw [actionCorank, hfixed]
  have hLC : L ⊓ M ≤ M ⊓ centralizer (U : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hL.1)
  have hgen (hg : V = U ⊔ ⁅V, L ⊓ M⁆) :=
    (h.action_escape_of_decomposition hU hn hLC hg).2
  rcases RemainingSieve.adequateComponentAlternatives_knownSimple h hU hL with
    ⟨n, hb⟩ | ⟨n, hs⟩ | hfour | ha | hodd
  · have hn' : 1 < n := by rw [hb.dimension, hcor]; exact hn
    apply hgen
    simpa only [hfixed, sup_comm] using (hb.decomposition hn').1.symm
  · rcases hs.local_structure with ⟨_, hb⟩ | ⟨_, _, he⟩
    · rcases hb with ⟨_, A, hUA, hAV, _, hesc⟩ | ⟨_, he⟩
      · exact (hesc (inf_le_right.trans (hmax A hUA hAV.le))).elim
      · rw [hcor] at he
        omega
    · have hn' : 1 < n := by rw [← he, hcor]; exact hn
      apply hgen
      simpa only [hfixed, sup_comm] using (hs.decomposition hn').1.symm
  · have he := hfour.2.2.1
    rw [hcor] at he
    omega
  · obtain ⟨A, hUA, hAV, he, hesc⟩ := ha.escape
    have hlt : U < A := lt_of_le_of_ne hUA (by
      intro heq
      rw [← heq] at he
      omega)
    exact (hesc (inf_le_right.trans (hmax A hlt hAV))).elim
  · have he := hodd.2.1
    rw [hcor] at he
    omega

/-- The moving-element consequence of E.6.11(2), with every preceding source
premise discharged for the full known-simple catalogue. -/
theorem maximal_escape_action_knownSimple
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hU : U ∈ obstructionFamily M V)
    (hmax : ∀ W : Subgroup G, U < W → W ≤ V → centralizer (W : Set G) ≤ M)
    (hn : 1 < subgroupCorank V U) :
    ∃ x ∈ M ⊓ centralizer (U : Set G), x ∉ centralizer (V : Set G) := by
  rcases component_or_characteristicTwo_of_maximal_escape h hU hmax hn with
    ⟨L, hL⟩ | hc
  · exact action_escape_of_component h hU hmax hn hL
  · exact action_escape_of_characteristicTwo h hU hmax hn hc

end CFSG.Quasithin.ChapterE.Section06
