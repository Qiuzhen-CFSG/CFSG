module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCommutingNaturalSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CoreProductComparison
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NaturalBranch
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.AdjacentParameterEquality
public import Theory.SpecificGroups.SL2.FieldCardinality
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# Actual Chapter 12 data for an original commuting A5 pair

The original A5 quotient marks supply the full edge two-core product and
common local Sylows. The verified commuting natural-center theorem then gives
centerlessness on the natural orbit, central neighboring centers, their
inclusion in each adjacent natural center, and the exact radius-one/core
commutator. Natural coordinates prove center orders sixteen and four and
minimality under the actual local actor. Reciprocal source critical geometry
gives both opposite span/core indices four and crossed-intersection commutation.

Every theorem takes the full original F.1.1 hypotheses and actual quotient
marks. No common Sylow, naturality, center order, irreducibility, catalogue,
core equality, or containment is supplied as a caller premise. The geometry
may be an arbitrary directed critical first edge. These are the actual fields
needed in (12.1); the conjugated intersection index and residual-section
assembly of (12.3)(a,c) remain separate source obligations.

Source: DGS, Groups and Graphs (1985), (8.1), (8.6)--(8.7), (12.1),
printed pp.132--140,178; (12.3), pp.179--180.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open CFSG.Quasithin.ChapterF.Source CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

theorem a5_pair_reduced_edge_sylows (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {x y : Vertex (Reduction.reducedFamily L S)}
    (hxy : (graph (Reduction.reducedFamily L S)).Adj x y) :
    let F := Reduction.reducedFamily L S
    Q F x ⊔ Q F y = (stabilizer F x ⊓ stabilizer F y).pCoreIn 2 ∧
      ∃ T : Sylow 2 (graphLocalGroup F x),
        (T : Subgroup (graphLocalGroup F x)).map (graphLocalGroup F x).subtype =
          Q F x ⊔ Q F y := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  obtain ⟨T, hT⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d hxy
  have hi := a5_pair_reduced_graph_linear_four h a x
  have hprod := source_linear_edge_core_product ht d hxy (.linear 2 (by decide) hi) T hT
    (Reduction.reduced_graph_core_obstruction h y x hxy.symm) (by decide : 0 < 2) hi
  exact ⟨hprod, T, hT.trans hprod.symm⟩

theorem a5_pair_commuting_orbit_geometry
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v u w : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v w)
    (hvu : (graph (Reduction.reducedFamily L S)).Adj v u)
    (hd : (graph (Reduction.reducedFamily L S)).dist u w + 1 =
      b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) v, Z (Reduction.reducedFamily L S) w⁆ = ⊥)
    {x y : Vertex (Reduction.reducedFamily L S)}
    (hxy : (graph (Reduction.reducedFamily L S)).Adj x y)
    (htx : v.type = x.type) :
    let F := Reduction.reducedFamily L S
    Noncommuting.HasNaturalCenter (graphLocalGroup F x) (Z F x) (Q F x) ∧
      center (graphLocalGroup F x) = ⊥ ∧
      Z F y = omegaCenterIn (graphLocalGroup F y) ∧ Z F y ≤ Z F x ∧
      ⁅V F y 1, Q F y⁆ = Z F y := by
  let F := Reduction.reducedFamily L S
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  obtain ⟨hb3, _, hnat⟩ := a5_pair_commuting_critical_natural h a hc hvu hd hcomm
  have hb : 1 < b F := by
    change 1 < b (Reduction.reducedFamily L S)
    omega
  have hcu := (source_critical_geometry ht d hc hvu hd hb hcomm).2.2.1
  have hty : u.type = y.type := by
    have hvu' := hvu.1
    have hxy' := hxy.1
    cases hv : v.type <;> cases hu : u.type <;> cases hx : x.type <;>
      cases hy : y.type <;> simp_all
  have hcy : Z F y = omegaCenterIn (graphLocalGroup F y) :=
    (Noncommuting.graph_center_equality_of_type ht d.localGroup d.conjugate hty).mp hcu
  have hnx := source_natural_center_of_type ht d htx hnat
  have hcenter := local_center_eq_bot_of_neighbor_central ht d hxy hcy
  have hseed := source_central_edge_seed ht (Reduction.reduced_borel_core_sylow h) d hxy hcy
  have hle : Z F y ≤ Z F x := hseed.1.symm ▸ hseed.2
  have hedge : ⁅Z F x, Q F y⁆ = Z F y := source_natural_edge_commutator ht
    (Reduction.reduced_borel_core_sylow h) d hxy hcy hnx (Q F y)
    (by
      change Q F y ≤ (stabilizer F x ⊓ stabilizer F y).pCoreIn 2
      have hh := Noncommuting.graph_Q_le_edgeCore ht hxy.symm
      change Q F y ≤ (stabilizer F y ⊓ stabilizer F x).pCoreIn 2 at hh
      rwa [inf_comm] at hh)
    (CommutingTrivial.core_escape_of_intersection_obstruction F
      (Reduction.reduced_graph_core_obstruction h y x hxy.symm))
  have hzne : Z F y ≠ ⊥ := by
    obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base F y
    let : ∀ i, Finite (F i) := finite_endpoints ht
    intro hz
    rw [← hg, Z_translate] at hz
    exact base_Z_ne_bot ht y.type
      ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hz)
  have hVne : ⁅V F y 1, Q F y⁆ ≠ ⊥ := by
    intro hz
    apply hzne
    rw [← hedge]
    exact bot_unique ((commutator_mono (Z_neighbor_le_V F hxy.symm) le_rfl).trans hz.le)
  exact ⟨hnx, hcenter, hcy, hle,
    source_natural_span_commutator ht (Reduction.reduced_borel_core_sylow h) d
      hvu hty hcu hnat (Q F y) le_rfl hVne⟩

theorem a5_pair_commuting_intersection_commutes
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v u w : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v w)
    (hvu : (graph (Reduction.reducedFamily L S)).Adj v u)
    (hd : (graph (Reduction.reducedFamily L S)).dist u w + 1 =
      b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) v, Z (Reduction.reducedFamily L S) w⁆ = ⊥) :
    let F := Reduction.reducedFamily L S
    ⁅V F u 1 ⊓ Q F w, V F w 1 ⊓ Q F u⁆ = ⊥ := by
  have models (z : Vertex (Reduction.reducedFamily L S)) :
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S) z ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) z)) :=
    .linear 2 (by decide) (a5_pair_reduced_graph_linear_four h a z)
  obtain ⟨hb3, hne⟩ := a5_pair_commuting_critical_remaining h a hc hvu hd hcomm
  have hnat := (a5_pair_commuting_critical_natural h a hc hvu hd hcomm).2.2
  exact reduced_natural_start_intersection_commutes h (Reduction.reduced_graph_core_obstruction h)
    models hc hvu hd (by omega) hcomm hne hnat

theorem a5_pair_commuting_center_card_and_minimal
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v u w : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v w)
    (hvu : (graph (Reduction.reducedFamily L S)).Adj v u)
    (hd : (graph (Reduction.reducedFamily L S)).dist u w + 1 =
      b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) v, Z (Reduction.reducedFamily L S) w⁆ = ⊥)
    {x y : Vertex (Reduction.reducedFamily L S)}
    (hxy : (graph (Reduction.reducedFamily L S)).Adj x y)
    (htx : v.type = x.type) :
    let F := Reduction.reducedFamily L S
    Nat.card (Z F x) = 16 ∧
      ∀ D : Subgroup (Reduction.G₀ L S), D ≤ Z F x →
        graphLocalGroup F x ≤ normalizer (D : Set (Reduction.G₀ L S)) →
        D = ⊥ ∨ D = Z F x := by
  let F := Reduction.reducedFamily L S
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  obtain ⟨hnat, _, hcy, _⟩ := a5_pair_commuting_orbit_geometry h a hc hvu hd hcomm hxy htx
  obtain ⟨K, _, _, _, π, e, hπ, _, _, ⟨δ⟩⟩ :=
    source_natural_center_coordinates_of_neighbor_central ht d hxy hcy hnat
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  obtain ⟨E, _, _, hE, ⟨eE⟩⟩ := a5_pair_reduced_graph_linear_four h a x
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  let eSL := eE.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi E)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
  have hK : Nat.card K = 4 := (Matrix.SL2.field_card_eq_of_equiv (e.symm.trans eSL)).trans hE
  have hcard := δ.card_section
  have hinj : Function.Injective δ.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [δ.kernel_eq, bot_subgroupOf]
  refine ⟨?_, ?_⟩
  · norm_num only [Nat.card_fun, Nat.card_fin, Nat.card_unique, hK, mul_one] at hcard
    exact hcard
  intro D hDZ hnorm
  by_cases hzero : D = ⊥
  · exact Or.inl hzero
  right
  obtain ⟨c, hcD, hcne⟩ := D.bot_or_exists_ne_one.resolve_left hzero
  let cZ : Z F x := ⟨c, hDZ hcD⟩
  have hc0 : (δ.coordinates cZ).toAdd ≠ 0 := by
    intro he
    have hh : δ.coordinates cZ = 1 := Multiplicative.toAdd.injective he
    have hh' : cZ = 1 := hinj (hh.trans δ.coordinates.map_one.symm)
    exact hcne (congrArg Subtype.val hh')
  apply le_antisymm hDZ
  intro z hz
  by_cases hz1 : z = 1
  · exact hz1 ▸ D.one_mem
  let zZ : Z F x := ⟨z, hz⟩
  have hz0 : (δ.coordinates zZ).toAdd ≠ 0 := by
    intro he
    have hh : δ.coordinates zZ = 1 := Multiplicative.toAdd.injective he
    have hh' : zZ = 1 := hinj (hh.trans δ.coordinates.map_one.symm)
    exact hz1 (congrArg Subtype.val hh')
  obtain ⟨g, hg⟩ := Matrix.SL2.exists_mulVec_eq K
    (δ.coordinates cZ).toAdd (δ.coordinates zZ).toAdd hc0 hz0
  obtain ⟨l, rfl⟩ := hπ g
  have he := δ.equivariant l cZ
  change (δ.coordinates _).toAdd = Matrix.mulVec (π l).val (δ.coordinates cZ).toAdd at he
  have heq := hinj (Multiplicative.toAdd.injective (he.trans hg))
  have hzval : (l : Reduction.G₀ L S) * c * (l : Reduction.G₀ L S)⁻¹ = z :=
    congrArg Subtype.val heq
  exact hzval ▸ (mem_normalizer_iff.mp (hnorm l.property) c).mp hcD

theorem a5_pair_commuting_span_core_index
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v u w : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v w)
    (hvu : (graph (Reduction.reducedFamily L S)).Adj v u)
    (hd : (graph (Reduction.reducedFamily L S)).dist u w + 1 =
      b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) v, Z (Reduction.reducedFamily L S) w⁆ = ⊥) :
    (Q (Reduction.reducedFamily L S) u).relIndex (V (Reduction.reducedFamily L S) w 1) = 4 := by
  let : ∀ i, Finite (Reduction.reducedFamily L S i) :=
    finite_endpoints (Reduction.reduced_triple h)
  let : Finite (graphLocalGroup (Reduction.reducedFamily L S) u) :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have models (z : Vertex (Reduction.reducedFamily L S)) :
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S) z ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) z)) :=
    .linear 2 (by decide) (a5_pair_reduced_graph_linear_four h a z)
  obtain ⟨hb3, hne⟩ := a5_pair_commuting_critical_remaining h a hc hvu hd hcomm
  have hnat := (a5_pair_commuting_critical_natural h a hc hvu hd hcomm).2.2
  obtain ⟨R, hR⟩ := reduced_natural_start_opposite_omega_index h models hc hvu hd
    (by omega) hcomm hne hnat
  obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := a5_pair_reduced_graph_linear_four h a u
  let := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let e := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
  exact hR.trans ((CommutingTrivial.linear_marking_quotient_sylow_omega_card e R).trans hK)

theorem a5_pair_commuting_both_span_core_indices
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v u w : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v w)
    (hvu : (graph (Reduction.reducedFamily L S)).Adj v u)
    (hd : (graph (Reduction.reducedFamily L S)).dist u w + 1 =
      b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) v, Z (Reduction.reducedFamily L S) w⁆ = ⊥) :
    let F := Reduction.reducedFamily L S
    (Q F u).relIndex (V F w 1) = 4 ∧ (Q F w).relIndex (V F u 1) = 4 := by
  have models (z : Vertex (Reduction.reducedFamily L S)) :
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S) z ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) z)) :=
    .linear 2 (by decide) (a5_pair_reduced_graph_linear_four h a z)
  obtain ⟨hb3, hne⟩ := a5_pair_commuting_critical_remaining h a hc hvu hd hcomm
  obtain ⟨_, z, hzw, hcz, hdz, hcommz, _⟩ := reduced_reciprocal_critical_configuration h
    (Reduction.reduced_graph_core_obstruction h) models hc hvu hd (by omega) hcomm hne
  exact ⟨a5_pair_commuting_span_core_index h a hc hvu hd hcomm, a5_pair_commuting_span_core_index h a hcz hzw hdz hcommz⟩

theorem a5_pair_commuting_neighboring_center_card
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v u w : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v w)
    (hvu : (graph (Reduction.reducedFamily L S)).Adj v u)
    (hd : (graph (Reduction.reducedFamily L S)).dist u w + 1 =
      b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) v, Z (Reduction.reducedFamily L S) w⁆ = ⊥)
    {x y : Vertex (Reduction.reducedFamily L S)}
    (hxy : (graph (Reduction.reducedFamily L S)).Adj x y)
    (htx : v.type = x.type) : Nat.card (Z (Reduction.reducedFamily L S) y) = 4 := by
  let F := Reduction.reducedFamily L S
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  obtain ⟨hnat, _, hcy, hle, _⟩ := a5_pair_commuting_orbit_geometry h a hc hvu hd hcomm hxy htx
  obtain ⟨K, _, _, _, π, e, hπ, _, _, ⟨δ⟩⟩ :=
    source_natural_center_coordinates_of_neighbor_central ht d hxy hcy hnat
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  obtain ⟨E, _, _, hE, ⟨eE⟩⟩ := a5_pair_reduced_graph_linear_four h a x
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  let eSL := eE.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi E)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
  have hK : Nat.card K = 4 := (Matrix.SL2.field_card_eq_of_equiv (e.symm.trans eSL)).trans hE
  let A := d.localGroup x
  let B := (stabilizer F x ⊓ stabilizer F y).pCoreIn 2
  let : Finite (d.localGroup x) :=
    Finite.of_injective (inclusion (d.local_le x)) (inclusion_injective _)
  obtain ⟨R, hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d hxy
  change (R : Subgroup A).map A.subtype = B at hR
  have hBA : B ≤ A := by
    rw [← hR]
    exact map_subtype_le (R : Subgroup A)
  let T := R.mapSurjective (f := π) hπ
  have hT : (B.subgroupOf A).map π = T := by
    have heq : B.subgroupOf A = R := by
      apply map_injective A.subtype_injective
      rw [map_subgroupOf_eq_of_le hBA]
      exact hR.symm
    rw [heq]
    rfl
  have hTne : (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) ≠ ⊥ := by
    intro heq
    have hh := Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 T).symm.toEquiv
    rw [heq, Nat.card_unique] at hh
    change 1 = Nat.card K at hh
    omega
  have hBesc : ¬ B ≤ Q F x := by
    intro hh
    apply CommutingTrivial.core_escape_of_intersection_obstruction F
      (Reduction.reduced_graph_core_obstruction h y x hxy.symm)
    have hQy := Noncommuting.graph_Q_le_edgeCore ht hxy.symm
    change Q F y ≤ (stabilizer F y ⊓ stabilizer F x).pCoreIn 2 at hQy
    rw [inf_comm] at hQy
    exact hQy.trans hh
  have hedge : ⁅Z F x, B⁆ = Z F y := source_natural_edge_commutator ht
    (Reduction.reduced_borel_core_sylow h) d hxy hcy hnat B le_rfl hBesc
  let N := Representation.SL2NaturalOffenders.NoStrong.natural (F := K)
  have hself : δ.imageSpace (Z F x) = ⊤ := δ.imageSpace_self
  have him : δ.imageSpace (Z F y) = Representation.BinaryOffender.fixedSpace N T := by
    rw [←hedge, commutator_comm, δ.imageSpace_commutator B (Z F x) hBA le_rfl,
      hself, Representation.BinaryOffender.subspaceCommutator_comp_map, hT]
    exact (Noncommuting.natural_subgroup_fixed_moved T T le_rfl hTne).2
  let et : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K := Subgroup.topEquiv
  let P := T.mapSurjective (f := et.symm.toMonoidHom) et.symm.surjective
  have heP : (P : Subgroup (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))).map
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)).subtype = T := by
    change ((T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)).map et.symm.toMonoidHom).map _ = _
    rw [map_map]
    exact map_id _
  have hcod := Representation.SL2NaturalOffenders.Ratios.sylowImage_fixedCodim
    ⊤ et N (fun _ _ => rfl) P
  rw [heP] at hcod
  have hadd := Representation.BinaryOffender.fixedCodim_add_finrank N (T : Subgroup _)
  have hdim : Module.finrank (ZMod 2) (Fin 2 → K) = 2 * Module.finrank (ZMod 2) K := by
    simp [Module.finrank_pi_fintype, two_mul]
  have hfix : Module.finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace N T) =
      Module.finrank (ZMod 2) K := by omega
  have hcard := δ.imageSpace_card_eq_relIndex (Z F y) hle
  rw [relIndex_bot_left, him, Module.natCard_eq_pow_finrank (K := ZMod 2), hfix] at hcard
  exact hcard.symm.trans ((Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)).symm.trans hK)
end CFSG.Quasithin.ChapterF.Source
