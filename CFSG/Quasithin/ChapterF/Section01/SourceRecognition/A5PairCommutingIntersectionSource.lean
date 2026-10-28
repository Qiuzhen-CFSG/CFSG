module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCommutingChapterTwelveSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.FullEdgeComplements
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearComplementTransitivity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiInitialSylow

/-!
# The actual conjugated intersection index for a commuting A5 pair

Both original A5 marks give linear local quotients at every graph vertex.
The full adjacent-core product and the actual local affine action make the
opposite core transitive on the remaining neighbors. This constructs an odd
full-edge complement fixing the second intersection vertex, then its literal
middle-core conjugate fixing a selected moving neighbor. Full edge conjugacy
preserves its complement property. Restriction to the actual starred endpoint
and its marked Sylow normalizer makes the nonzero intersection image the
whole field-four root group.

Conjugation at the terminal vertex now constructs the source vertex sigma.
The crossed commutator is zero, the opposite span/core index is four, and the
intersection image at the prescribed middle vertex has order four. These are
the genuine conjugated data needed by the central case of (12.3)(c); no
complement, transitivity, quotient image, or index callback is supplied.

Source: DGS, Groups and Graphs (1985), (12.3)(a,c), printed pp.179--180.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open CFSG.Quasithin.ChapterF.Source CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

theorem a5_pair_reduced_core_transitive (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v w : Vertex (Reduction.reducedFamily L S)}
    (hvw : (graph (Reduction.reducedFamily L S)).Adj v w)
    {x y : Vertex (Reduction.reducedFamily L S)}
    (hx : (graph (Reduction.reducedFamily L S)).Adj v x)
    (hy : (graph (Reduction.reducedFamily L S)).Adj v y)
    (hxw : x ≠ w) (hyw : y ≠ w) :
    ∃ q ∈ Q (Reduction.reducedFamily L S) w, q • x = y := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  have hi := a5_pair_reduced_graph_linear_four h a v
  let M := IsRankOneModel.linear 2 (by decide) hi
  obtain ⟨R, hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d hvw
  have hprod := (a5_pair_reduced_edge_sylows h a hvw).1
  have htrans := source_edge_transitive_or_dihedral ht (Reduction.reduced_borel_core_sylow h) d hvw M
  rcases htrans with htrans | ⟨ed⟩
  · exact source_full_product_core_transitive ht d hvw M R hR hprod htrans hx hy hxw hyw
  · obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := hi
    let := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hK)
    let e := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
    have hc := Nat.card_congr (ed.some.symm.trans e).toEquiv
    rw [DihedralGroup.nat_card, BenderSuzuki.External.huppert614_card_specialLinearGroup, hK] at hc
    norm_num at hc

theorem a5_pair_reduced_edge_complements (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {x m y z : Vertex (Reduction.reducedFamily L S)}
    (hxm : (graph (Reduction.reducedFamily L S)).Adj x m)
    (hym : (graph (Reduction.reducedFamily L S)).Adj y m)
    (hyx : y ≠ x)
    (hyz : (graph (Reduction.reducedFamily L S)).Adj y z) (hzm : z ≠ m) :
    let F := Reduction.reducedFamily L S
    let E := stabilizer F x ⊓ stabilizer F m
    let W := V F x 1 ⊓ Q F y
    ∃ K : Subgroup E,
      (pCore 2 E).IsComplement' K ∧ Odd (Nat.card K) ∧
      K.map E.subtype ≤ stabilizer F y ∧
      ∃ q ∈ Q F m,
        (K.map E.subtype).map (MulAut.conj q).toMonoidHom ≤
          stabilizer F x ⊓ stabilizer F y ⊓ stabilizer F z ∧
        (pCore 2 (stabilizer F y ⊓ stabilizer F z : Subgroup (Reduction.G₀ L S))).IsComplement'
          (((K.map E.subtype).map (MulAut.conj q).toMonoidHom).subgroupOf
            (stabilizer F y ⊓ stabilizer F z)) ∧
        (K.map E.subtype).map (MulAut.conj q).toMonoidHom ≤ normalizer (W : Set (Reduction.G₀ L S)) ∧
        Nat.card ((K.map E.subtype).map (MulAut.conj q).toMonoidHom) = Nat.card K := by
  let F := Reduction.reducedFamily L S
  let E := stabilizer F x ⊓ stabilizer F m
  obtain ⟨K, hK, hodd, hKy, _⟩ := source_edge_complement_fixing_neighbor h hxm hym hyx (by
    intro z hz hzx
    obtain ⟨t, ht, he⟩ := a5_pair_reduced_core_transitive h a hxm.symm hym.symm hz hyx hzx
    exact ⟨t, Noncommuting.graph_Q_le_edgeCore (Reduction.reduced_triple h) hxm ht, he⟩)
  have hcK : Nat.card (K.map E.subtype) = Nat.card K :=
    Nat.card_congr (K.equivMapOfInjective E.subtype E.subtype_injective).symm.toEquiv
  obtain ⟨q, hq, hfix, hnorm, hcard, _⟩ := source_middle_core_conjugate_complement h
    hxm hym hyz hzm (K.map E.subtype)
    ((map_subtype_le K).trans inf_le_left) ((map_subtype_le K).trans inf_le_right)
    hKy (hcK.symm ▸ hodd) (fun w hw hwm => a5_pair_reduced_core_transitive h a hym hyz hw hzm hwm)
  have hcard' := hcard.trans hcK
  have hnew := source_edge_complement_transfer h hxm hyz K hK
    ((K.map E.subtype).map (MulAut.conj q).toMonoidHom)
    (le_inf (hfix.trans (inf_le_left.trans inf_le_right)) (hfix.trans inf_le_right))
    (hcard'.symm ▸ hodd) hcard'
  exact ⟨K, hK, hodd, hKy, q, hq, hfix, hnew, hnorm, hcard'⟩


theorem a5_pair_commuting_moved_intersection_index
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v u w m : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v w)
    (hvu : (graph (Reduction.reducedFamily L S)).Adj v u)
    (hd : (graph (Reduction.reducedFamily L S)).dist u w + 1 =
      b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) v, Z (Reduction.reducedFamily L S) w⁆ = ⊥)
    (hum : (graph (Reduction.reducedFamily L S)).Adj u m)
    (hwm : (graph (Reduction.reducedFamily L S)).Adj w m) :
    let F := Reduction.reducedFamily L S
    ∃ z, (graph F).Adj w z ∧ z ≠ m ∧
      ⁅V F u 1 ⊓ Q F w, Z F z⁆ ≠ ⊥ ∧
      (Q F z).relIndex (V F u 1 ⊓ Q F w) = 4 := by
  let F := Reduction.reducedFamily L S
  obtain ⟨hb3, hne⟩ := a5_pair_commuting_critical_remaining h a hc hvu hd hcomm
  have hb : 2 < b F := by
    change 2 < b (Reduction.reducedFamily L S)
    omega
  have hwu : w ≠ u := by
    intro he
    rw [he, SimpleGraph.dist_self] at hd
    omega
  obtain ⟨_, z, hz, hzm, hmove, hesc, _⟩ :=
    source_intersection_moved_neighbor h hb hum hwm hne
  obtain ⟨K, hK, hodd, hKw, q, hq, hfix, hnew, hnorm, hcard⟩ :=
    a5_pair_reduced_edge_complements h a hum hwm hwu hz hzm
  have hc4 : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by decide)
  let e4 := (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (by simpa using hc4)).some
  let ep := MulEquiv.ofBijective (BenderSuzuki.Converse.pi (GaloisField 2 2))
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  let e := (a (if z.type then 1 else 0)).some.trans (e4.symm.trans ep.symm)
  obtain ⟨T, hT⟩ := source_linear_initial_sylow h z.type (by decide : 0 < 2) hc4 e
  let E := stabilizer F u ⊓ stabilizer F m
  let C := (K.map E.subtype).map (MulAut.conj q).toMonoidHom
  have hC : C ≤ stabilizer F w ⊓ stabilizer F z :=
    le_inf (hfix.trans (inf_le_left.trans inf_le_right)) (hfix.trans inf_le_right)
  have hi := (linear_complement_invariant_transitive_at h z.type e T hT rfl hz.symm
    (V F u 1 ⊓ Q F w) C inf_le_right hesc hC hnew (hcard.symm ▸ hodd) hnorm).1
  exact ⟨z, hz, hzm, hmove, hi.trans hc4⟩


theorem a5_pair_commuting_conjugated_intersection_indices
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v u w m : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v w)
    (hvu : (graph (Reduction.reducedFamily L S)).Adj v u)
    (hd : (graph (Reduction.reducedFamily L S)).dist u w + 1 =
      b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) v, Z (Reduction.reducedFamily L S) w⁆ = ⊥)
    (hum : (graph (Reduction.reducedFamily L S)).Adj u m)
    (hwm : (graph (Reduction.reducedFamily L S)).Adj w m) :
    let F := Reduction.reducedFamily L S
    ∃ σ : Vertex F,
      ⁅V F w 1 ⊓ Q F σ, V F σ 1 ⊓ Q F w⁆ = ⊥ ∧
      (Q F σ).relIndex (V F w 1) = 4 ∧
      (Q F m).relIndex (V F σ 1 ⊓ Q F w) = 4 := by
  let F := Reduction.reducedFamily L S
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  obtain ⟨z, hz, _, _, hi⟩ := a5_pair_commuting_moved_intersection_index h a hc hvu hd hcomm hum hwm
  obtain ⟨g, hg, hgz⟩ := d.transitive w ⟨z, hz⟩ ⟨m, hwm⟩
  have hgw : g • w = w := d.local_le w hg
  have hgc : IsCriticalPair F (g • v) w := by
    have hh := criticalPair_translate F hc g
    rwa [hgw] at hh
  have hga : (graph F).Adj (g • v) (g • u) :=
    (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hvu
  have hgd : (graph F).dist (g • u) w + 1 = b F := by
    rw [←hgw, Subgroup.CosetGeometry.RankTwo.dist_smul]
    exact hd
  have hcommg : ⁅Z F (g • v), Z F w⁆ = ⊥ := by
    rw [←hgw, commuting_centers_translate, hcomm, Subgroup.map_bot]
  have hcross := a5_pair_commuting_intersection_commutes h a hgc hga hgd hcommg
  dsimp only at hcross
  have hsmall := a5_pair_commuting_span_core_index h a hgc hga hgd hcommg
  have hi' := relIndex_map_map_of_injective (Q F z) (V F u 1 ⊓ Q F w)
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [map_inf _ _ _ (MulAut.conj g).injective, ←Q_translate, ←V_translate,
    ←Q_translate, hgz, hgw, hi] at hi'
  exact ⟨g • u, by rwa [commutator_comm] at hcross, hsmall, hi'⟩

end CFSG.Quasithin.ChapterF.Source
