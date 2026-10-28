module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.LocalIncidence.RootReduction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.LocalIncidence.RootModelGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.LocalIncidence.PureFourCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.AlternatingFiveGeometry.Edges
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.EdgeCentralizer
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicEdgeIncidence
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.ExternalOrbit

/-!
# Local triple incidence at an edge

For an outer conjugate, the literal D₁₀ intersection has A₅ centralizer
by the five-local normalizer theorem. The whole triple lies in this same
centralizer. The marked cubic-subgroup calculation gives the three vertices
in its X-orbit, the unique common neighbor, and the other two A₅ joins.
The intersection model remains the independent double-coset calculation.

For an inner conjugate, the embedded O₂ of the A₄ intersection is a pure
four-group. Its proved full-centralizer identification and the intrinsic
Heisenberg-four cubic geometry give the SL₂(3) join for every X-translate.
Both model-construction premises of the inner reduction are discharged here.
The fixer model and its involution fusion are the preceding stabilizer
conclusions; the A₄ intersection remains the independent double-coset input.
Global orbit counts and the equality with the SL₂-join set belong to the
parent edge-configuration assembly.

Source: Aschbacher, *Sporadic Groups* (1994), 47.6(1),(2), pp.263–264.
-/

@[expose] public section
open Subgroup MulAction
open scoped Pointwise
open Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
open alternatingGroup.FiveLocalGeometry.CubicEdgeIncidence
variable {G : Type*} [Group G] [Finite G]

private theorem restrict_injective (D : Seed G) (K : Subgroup G)
    {V W : D.Vertex} (hV : V.val ≤ K) (hW : W.val ≤ K)
    (h : V.val.subgroupOf K = W.val.subgroupOf K) : V = W := by
  apply Subtype.ext
  have he := congrArg (fun S : Subgroup K => S.map K.subtype) h
  simpa only [map_subgroupOf_eq_of_le hV, map_subgroupOf_eq_of_le hW] using he

private theorem restrict_orbit (D : Seed G) (K : Subgroup G)
    (hX : D.X ≤ K) (U : D.Vertex) (hU : U.val ≤ K)
    {W : D.Vertex} (hW : W ∈ orbit D.X U) :
    W.val ≤ K ∧ W.val.subgroupOf K ∈
      cubicOrbit (D.X.subgroupOf K) (U.val.subgroupOf K) := by
  obtain ⟨x, rfl⟩ := hW
  let k : K := ⟨x, hX x.property⟩
  refine ⟨conj_smul_le_of_le hU k, ⟨⟨k, x.property⟩, ?_⟩⟩
  change MulAut.conj k • U.val.subgroupOf K = _
  rw [conj_smul_subgroupOf hU k]
  rfl

private theorem realize_orbit (D : Seed G) (K : Subgroup G)
    (_hX : D.X ≤ K) (U : D.Vertex) (hU : U.val ≤ K)
    (S : Subgroup K)
    (hS : S ∈ cubicOrbit (D.X.subgroupOf K) (U.val.subgroupOf K)) :
    ∃ W : D.Vertex, W ∈ orbit D.X U ∧ W.val ≤ K ∧ W.val.subgroupOf K = S := by
  obtain ⟨x, rfl⟩ := hS
  let a : D.X := ⟨(x : K), x.property⟩
  refine ⟨(a : G) • U, ⟨a, rfl⟩, conj_smul_le_of_le hU (x : K), ?_⟩
  change _ = MulAut.conj (x : K) • U.val.subgroupOf K
  rw [conj_smul_subgroupOf hU (x : K)]
  rfl

/-- Every translate in the X-orbit is still adjacent to X. -/
theorem orbit_neighbors (D : Seed G) {U W : D.Vertex}
    (hU : D.graph.Adj D.base U) (hW : W ∈ orbit D.X U) :
    D.graph.Adj D.base W := by
  obtain ⟨x, rfl⟩ := hW
  have h := D.preserves (x : G) hU
  rwa [normalizer_fixes_base D ⟨x, D.X.le_normalizer x.property⟩] at h

/-- The inner implication of 47.6(1), including every literal X-translate.
The pure four-group centralizer and its cubic geometry are both proved inputs;
only the preceding fixer facts and the actual A₄ intersection are retained. -/
theorem inner_sl2Join_translate (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ fixer D Y, orderOf t = 2 → IsConj D.z t)
    (g : localCentralizer D) (hg : (g : G) ∉ actor D Y)
    (hI : Nonempty (intersection D Y g ≃* alternatingGroup (Fin 4))) (x : D.X) :
    sl2Join D Y ((x : G) • ((g : G) • Y)) :=
  inner_sl2Join_of_heisenberg_geometry D (PureFourCentralizer.models D)
    Y hY hF hclass g hg hI.some x

/-- Each conjugate by L outside F ⊔ X generates SL₂(3) with Y. -/
theorem inner_sl2Join (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ fixer D Y, orderOf t = 2 → IsConj D.z t)
    (g : localCentralizer D) (hg : (g : G) ∉ actor D Y)
    (hI : Nonempty (intersection D Y g ≃* alternatingGroup (Fin 4))) :
    sl2Join D Y ((g : G) • Y) := by
  simpa only [Subgroup.coe_one, one_smul] using
    inner_sl2Join_translate D Y hY hF hclass g hg hI 1

/-- The inner set lies in the SL₂-join set. This is the inclusion required by
the parent's global count argument, with both root-model premises discharged. -/
theorem innerSet_subset_sl2Join (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ fixer D Y, orderOf t = 2 → IsConj D.z t)
    (hI : ∀ g : localCentralizer D, (g : G) ∉ actor D Y →
      Nonempty (intersection D Y g ≃* alternatingGroup (Fin 4))) :
    innerSet D Y ⊆ {U | sl2Join D Y U} := by
  rintro U ⟨g, hg, hgA, rfl⟩
  exact inner_sl2Join D Y hY hF hclass ⟨g, hg⟩ hgA (hI ⟨g, hg⟩ hgA)

/-- Every vertex of an inner X-orbit remains adjacent to X and generates
SL₂(3) with Y, using the same literal four-group centralizer throughout. -/
theorem inner_orbit_incidence (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ fixer D Y, orderOf t = 2 → IsConj D.z t)
    (hI : ∀ g : localCentralizer D, (g : G) ∉ actor D Y →
      Nonempty (intersection D Y g ≃* alternatingGroup (Fin 4)))
    (U : D.Vertex) (hU : U ∈ innerSet D Y) :
    ∀ W ∈ orbit D.X U, D.graph.Adj D.base W ∧ sl2Join D Y W := by
  obtain ⟨g, hg, hgA, rfl⟩ := hU
  have hUg : D.graph.Adj D.base (g • Y) := by
    have h := D.preserves g hY
    rwa [normalizer_fixes_base D ⟨g, Subgroup.centralizer_le_normalizer _ hg⟩] at h
  intro W hW
  refine ⟨orbit_neighbors D hUg hW, ?_⟩
  obtain ⟨x, rfl⟩ := hW
  exact inner_sl2Join_translate D Y hY hF hclass ⟨g, hg⟩ hgA (hI ⟨g, hg⟩ hgA) x

/-- Transport of the intrinsic A₅ calculation into the literal source vertices. -/
theorem partition_in_alternatingFive (D : Seed G) (K : Subgroup G)
    (eK : K ≃* alternatingGroup (Fin 5)) (Y U : D.Vertex)
    (hY : D.graph.Adj D.base Y) (hU : D.graph.Adj D.base U)
    (hXK : D.X ≤ K) (hYK : Y.val ≤ K) (hUK : U.val ≤ K)
    (hout : U ∉ endpointOrbit D Y) :
    ∃ W A B : D.Vertex, W ≠ A ∧ W ≠ B ∧ A ≠ B ∧
      orbit D.X U = {W, A, B} ∧ D.graph.Adj Y W ∧ a5Join D Y A ∧ a5Join D Y B := by
  have hc (V : D.Vertex) (hV : V.val ≤ K) : Nat.card (V.val.subgroupOf K) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hV).toEquiv, D.vertex_card]
  have hnot : U.val.subgroupOf K ∉
      cubicOrbit (D.X.subgroupOf K) (Y.val.subgroupOf K) := by
    intro h
    obtain ⟨V, hV, hVK, he⟩ := realize_orbit D K hXK Y hYK _ h
    exact hout ((restrict_injective D K hVK hUK he) ▸ hV)
  obtain ⟨S₀, S₁, S₂, h01, h02, h12, horb, hj, hj1, hj2⟩ :=
    external_orbit_partition eK (D.X.subgroupOf K) (Y.val.subgroupOf K)
      (U.val.subgroupOf K) (hc D.base hXK) (hc Y hYK) (hc U hUK)
      ((AlternatingFiveGeometry.joinSubgroupOfEquiv K D.X Y.val hXK hYK).trans hY.2.some)
      ((AlternatingFiveGeometry.joinSubgroupOfEquiv K D.X U.val hXK hUK).trans hU.2.some) hnot
  have hs0 : S₀ ∈ cubicOrbit (D.X.subgroupOf K) (U.val.subgroupOf K) := by rw [horb]; simp
  have hs1 : S₁ ∈ cubicOrbit (D.X.subgroupOf K) (U.val.subgroupOf K) := by rw [horb]; simp
  have hs2 : S₂ ∈ cubicOrbit (D.X.subgroupOf K) (U.val.subgroupOf K) := by rw [horb]; simp
  obtain ⟨W, hW, hWK, hw⟩ := realize_orbit D K hXK U hUK S₀ hs0
  obtain ⟨A, hA, hAK, ha⟩ := realize_orbit D K hXK U hUK S₁ hs1
  obtain ⟨B, hB, hBK, hb⟩ := realize_orbit D K hXK U hUK S₂ hs2
  have full (V : D.Vertex) (hV : V.val ≤ K)
      (ht : Y.val.subgroupOf K ⊔ V.val.subgroupOf K = ⊤) : a5Join D Y V := by
    exact ⟨(AlternatingFiveGeometry.joinSubgroupOfEquiv K Y.val V.val hYK hV).symm.trans
      ((MulEquiv.subgroupCongr ht).trans (Subgroup.topEquiv.trans eK))⟩
  refine ⟨W, A, B, ?_, ?_, ?_, ?_, ?_, full A hAK (ha ▸ hj1), full B hBK (hb ▸ hj2)⟩
  · intro h; exact h01 (hw.symm.trans (h ▸ ha))
  · intro h; exact h02 (hw.symm.trans (h ▸ hb))
  · intro h; exact h12 (ha.symm.trans (h ▸ hb))
  · ext V
    constructor
    · intro hV
      obtain ⟨hVK, hr⟩ := restrict_orbit D K hXK U hUK hV
      rw [horb] at hr
      rcases hr with he | he | he
      · exact Or.inl (restrict_injective D K hVK hWK (he.trans hw.symm))
      · exact Or.inr (Or.inl (restrict_injective D K hVK hAK (he.trans ha.symm)))
      · exact Or.inr (Or.inr (restrict_injective D K hVK hBK (he.trans hb.symm)))
    · rintro (rfl | rfl | h)
      · exact hW
      · exact hA
      · have he : V = B := h
        exact he.symm ▸ hB
  · apply (D.graph_adj_iff Y W).mpr
    exact ⟨(AlternatingFiveGeometry.joinSubgroupOfEquiv K Y.val W.val hYK hWK).symm.trans
      ((MulEquiv.subgroupCongr (by rw [hw])).trans hj.some)⟩

/-- An outer conjugate cannot lie in the endpoint X-orbit: its transporter
would then be a product of X and the pointwise fixer, both centralizing X. -/
theorem outer_not_endpointOrbit (D : Seed G) (Y U : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (hU : U ∈ outerSet D Y) : U ∉ endpointOrbit D Y := by
  obtain ⟨g, hg, hgL, rfl⟩ := hU
  rintro ⟨x, hx⟩
  have : IsCyclic D.X := isCyclic_of_prime_card D.card_X
  have hxL : (x : G) ∈ localCentralizer D :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance) x.property
  have hfx : x⁻¹ * g ∈ fixer D Y := by
    constructor
    · exact normalizer_fixes_base D
        ⟨x⁻¹ * g, (localNormalizer D).mul_mem
          ((localNormalizer D).inv_mem (D.X.le_normalizer x.property)) hg⟩
    · change ((x : G)⁻¹ * g) • Y = Y
      rw [mul_smul, ← hx]
      exact inv_smul_smul (x : G) Y
  have hL := (localCentralizer D).mul_mem hxL (fixer_le_localCentralizer D Y hF hfx)
  exact hgL (by simpa using hL)

/-- The D₁₀ model identifies the literal centralizer and retains all three
vertices in it. This is the exact use of the five-local source assumption. -/
theorem outer_triple_centralizer (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (h₅ : PrimeNormalizers.FiveNormalizerTypes G)
    (g : localNormalizer D) (hI : Nonempty (intersection D Y g ≃* DihedralGroup 5)) :
    Nonempty (centralizer (intersection D Y g : Set G) ≃* alternatingGroup (Fin 5)) ∧
      D.X ⊔ Y.val ⊔ ((g : G) • Y).val ≤ centralizer (intersection D Y g : Set G) := by
  let E : EdgeFrame D := ⟨Y, hY, intersection D Y g, inf_le_left, hI⟩
  exact ⟨PrimeNormalizers.edgeFrame_centralizer_equiv E hF h₅,
    triple_le_centralizer D Y hF g _ le_rfl⟩

/-- The outer X-orbit has one A₄ neighbor and two A₅ joins, as actual vertices.
No orbit size, incidence count or join type is an input. -/
theorem outer_orbit_partition (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (h₅ : PrimeNormalizers.FiveNormalizerTypes G)
    (hI : ∀ g : localNormalizer D, (g : G) ∉ localCentralizer D →
      Nonempty (intersection D Y g ≃* DihedralGroup 5))
    (U : D.Vertex) (hU : U ∈ outerSet D Y) :
    ∃ W A B : D.Vertex, W ≠ A ∧ W ≠ B ∧ A ≠ B ∧
      orbit D.X U = {W, A, B} ∧ D.graph.Adj Y W ∧ a5Join D Y A ∧ a5Join D Y B ∧
      ∀ V ∈ orbit D.X U, D.graph.Adj D.base V := by
  have hout := outer_not_endpointOrbit D Y U hF hU
  obtain ⟨g, hg, hgL, rfl⟩ := hU
  have hUg : D.graph.Adj D.base (g • Y) := by
    have h := D.preserves g hY
    rwa [normalizer_fixes_base D ⟨g, hg⟩] at h
  obtain ⟨eK, hK⟩ := outer_triple_centralizer D Y hY hF h₅ ⟨g, hg⟩ (hI ⟨g, hg⟩ hgL)
  obtain ⟨W, A, B, hWA, hWB, hAB, horb, hw, ha, hb⟩ :=
    partition_in_alternatingFive D _ eK.some Y (g • Y) hY hUg
      (le_sup_left.trans (le_sup_left.trans hK)) (le_sup_right.trans (le_sup_left.trans hK))
      (le_sup_right.trans hK) hout
  exact ⟨W, A, B, hWA, hWB, hAB, horb, hw, ha, hb,
    fun _ hV => orbit_neighbors D hUg hV⟩

private theorem adj_not_a5 (D : Seed G) {Y W : D.Vertex}
    (h : D.graph.Adj Y W) : ¬ a5Join D Y W := by
  intro ha
  have h1 := card_join_of_adj D h
  have h2 := card_join_of_a5Join D ha
  omega

/-- The literal unique common neighbor required by `ExternalOrbit`.
The witness is constructed inside C_G(F ∩ Fᵍ). -/
theorem outer_unique_common_neighbor (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (h₅ : PrimeNormalizers.FiveNormalizerTypes G)
    (hI : ∀ g : localNormalizer D, (g : G) ∉ localCentralizer D →
      Nonempty (intersection D Y g ≃* DihedralGroup 5))
    (U : D.Vertex) (hU : U ∈ outerSet D Y) :
    ∃! W : D.Vertex, W ∈ orbit D.X U ∧ D.graph.Adj Y W := by
  obtain ⟨W, A, B, _, _, _, horb, hw, ha, hb, _⟩ :=
    outer_orbit_partition D Y hY hF h₅ hI U hU
  refine ⟨W, ⟨by rw [horb]; simp, hw⟩, ?_⟩
  rintro V ⟨hv, hadj⟩
  rw [horb] at hv
  rcases hv with h | h | h
  · exact h
  · exact False.elim (adj_not_a5 D (h ▸ hadj) ha)
  · have he : V = B := h
    exact False.elim (adj_not_a5 D (he ▸ hadj) hb)

/-- Each outer X-orbit has exactly three vertices. -/
theorem outer_orbit_card (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (h₅ : PrimeNormalizers.FiveNormalizerTypes G)
    (hI : ∀ g : localNormalizer D, (g : G) ∉ localCentralizer D →
      Nonempty (intersection D Y g ≃* DihedralGroup 5))
    (U : D.Vertex) (hU : U ∈ outerSet D Y) : Nat.card (orbit D.X U) = 3 := by
  obtain ⟨W, A, B, hWA, hWB, hAB, horb, _⟩ :=
    outer_orbit_partition D Y hY hF h₅ hI U hU
  rw [Nat.card_coe_set_eq, horb, Set.ncard_insert_of_notMem (by simpa using And.intro hWA hWB),
    Set.ncard_pair hAB]

/-- The other two vertices form precisely the A₅-join subset. The displayed
union is exhaustive and disjoint, retaining the unique adjacent vertex. -/
theorem outer_incidence_partition (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (h₅ : PrimeNormalizers.FiveNormalizerTypes G)
    (hI : ∀ g : localNormalizer D, (g : G) ∉ localCentralizer D →
      Nonempty (intersection D Y g ≃* DihedralGroup 5))
    (U : D.Vertex) (hU : U ∈ outerSet D Y) :
    ∃ W A B : D.Vertex, A ≠ B ∧
      {V ∈ orbit D.X U | D.graph.Adj Y V} = {W} ∧
      {V ∈ orbit D.X U | a5Join D Y V} = {A, B} ∧
      Nat.card {V : D.Vertex // V ∈ orbit D.X U ∧ a5Join D Y V} = 2 ∧
      orbit D.X U = {W} ∪ {A, B} ∧ Disjoint ({W} : Set D.Vertex) {A, B} ∧
      ∀ V ∈ orbit D.X U, D.graph.Adj D.base V := by
  obtain ⟨W, A, B, hWA, hWB, hAB, horb, hw, ha, hb, hbase⟩ :=
    outer_orbit_partition D Y hY hF h₅ hI U hU
  have hnw := adj_not_a5 D hw
  have hna : ¬ D.graph.Adj Y A := fun h => adj_not_a5 D h ha
  have hnb : ¬ D.graph.Adj Y B := fun h => adj_not_a5 D h hb
  have he : {V ∈ orbit D.X U | a5Join D Y V} = {A, B} := by
    ext V
    simp only [horb, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl, hv⟩
      · exact (hnw hv).elim
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), ha⟩
      · exact ⟨Or.inr (Or.inr rfl), hb⟩
  refine ⟨W, A, B, hAB, ?_, he, ?_, ?_, ?_, hbase⟩
  · ext V
    simp only [horb, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl, hv⟩
      · rfl
      · exact (hna hv).elim
      · exact (hnb hv).elim
    · rintro rfl
      exact ⟨Or.inl rfl, hw⟩
  · change Nat.card {V : D.Vertex | V ∈ orbit D.X U ∧ a5Join D Y V} = 2
    rw [Nat.card_coe_set_eq, he, Set.ncard_pair hAB]
  · rw [horb]
    ext V
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  · simp [hWA, hWB]

/-- Applying local uniqueness removes the X-component of the actor transporter.
The independent double-coset owner supplies only actor transitivity here. -/
theorem outer_common_transitive_of_intersections (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (h₅ : PrimeNormalizers.FiveNormalizerTypes G)
    (hI : ∀ g : localNormalizer D, (g : G) ∉ localCentralizer D →
      Nonempty (intersection D Y g ≃* DihedralGroup 5))
    (htrans : ∀ U ∈ outerSet D Y, ∀ V ∈ outerSet D Y,
      ∃ g : actor D Y, (g : G) • U = V)
    (U V : D.Vertex) (hU : U ∈ outerSet D Y) (hV : V ∈ outerSet D Y)
    (hUY : D.graph.Adj Y U) (hVY : D.graph.Adj Y V) :
    ∃ f : fixer D Y, (f : G) • U = V :=
  outer_common_transitive D Y hF htrans
    (outer_unique_common_neighbor D Y hY hF h₅ hI) U V hU hV hUY hVY

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
