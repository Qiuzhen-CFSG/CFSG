module
public import Theory.GroupAction.CoprimePointStabilizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EarlierInputs
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.IntersectionIndexSource

/-!
# Choosing the complements in DGS 12.3(a)

A full edge stabilizer is solvable and has normal Sylow two-subgroup, by
the actual F1.11 reduction. Given its Sylow transitivity on the remaining
neighbors at the linear middle vertex, construct an odd complement fixing
the second neighbor. It normalizes the literal V_x intersect Q_y.

If Q_m is transitive on the neighbors of y other than m, conjugate this
complement by an element of Q_m to fix a prescribed moved neighbor z.
Since Q_m fixes x and y, the conjugate still normalizes the same intersection.
Its order and its original ambient conjugation map are retained.

Source: DGS, Groups and Graphs (1985), 12.3(a), printed p.179.
The two local orbit statements remain explicit: they must follow from the
marked linear and opposite rank-one local actions in the Chapter 12
assembly. The dihedral exception uses its separate full-kernel containment.
No containment of the chosen full-edge complement in a starred endpoint,
or its linear quotient image, is asserted by these constructions.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
open Reduction
open Theory.GroupTheory.AmalgamGraph
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem reduced_edge_solvable (h : HypothesisF11 L S)
    {x m : Vertex (reducedFamily L S)} (hxm : (graph (reducedFamily L S)).Adj x m) :
    Group.IsSolvable (stabilizer (reducedFamily L S) x ⊓
      stabilizer (reducedFamily L S) m : Subgroup (G₀ L S)) := by
  let := h.commonBorel_solvable
  let : Group.IsSolvable (B₀ L S) := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (B₀_le h)) (inclusion_injective _)
  have hBG : B₀ L S ≤ G₀ L S :=
    (show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans le_sup_left
  let : Group.IsSolvable ((B₀ L S).subgroupOf (G₀ L S)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hBG).toMonoidHom) (subgroupOfEquivOfLe hBG).injective
  obtain ⟨g, _, he⟩ := source_edge_transport (reduced_triple h) hxm
  change stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) m = _ at he
  rw [he]
  exact Group.isSolvable_of_surjective
    (f := ((B₀ L S).subgroupOf (G₀ L S)).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective |>.toMonoidHom)
    (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).surjective

/-- Construct the full-edge complement fixing the second neighbor. -/
theorem source_edge_complement_fixing_neighbor (h : HypothesisF11 L S)
    {x m y : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj y m) (hyx : y ≠ x)
    (htrans : ∀ z, (graph (reducedFamily L S)).Adj m z → z ≠ x →
      ∃ t ∈ (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) m :
        Subgroup (G₀ L S)).pCoreIn 2, t • y = z) :
    let F := reducedFamily L S
    let E := stabilizer F x ⊓ stabilizer F m
    ∃ K : Subgroup E,
      (pCore 2 E).IsComplement' K ∧ Odd (Nat.card K) ∧
      K.map E.subtype ≤ stabilizer F y ∧
      K.map E.subtype ≤ normalizer (V F x 1 ⊓ Q F y : Set (G₀ L S)) := by
  let F := reducedFamily L S
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let E := stabilizer F x ⊓ stabilizer F m
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer F x from inf_le_left))
    (inclusion_injective _)
  have hs : ∃ T : Sylow 2 E, (T : Subgroup E) = pCore 2 E :=
    source_edge_core_sylow (reduced_triple h) (reduced_borel_core_sylow h) hxm
  obtain ⟨T, hT⟩ := hs
  let : (T : Subgroup E).Normal := hT ▸ inferInstance
  have horbit : ∀ g : E, ∃ t ∈ (T : Subgroup E), t • y = g • y := by
    intro g
    have hgm : (g : G₀ L S) • m = m := g.property.2
    have hgx : (g : G₀ L S) • x = x := g.property.1
    have hgy : (graph F).Adj m ((g : G₀ L S) • y) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F (g : G₀ L S)).map_adj_iff.mpr hym.symm
      change (graph F).Adj ((g : G₀ L S) • m) ((g : G₀ L S) • y) at hh
      rwa [hgm] at hh
    have hne : (g : G₀ L S) • y ≠ x := by
      intro he
      exact hyx ((MulAction.injective (g : G₀ L S)) (he.trans hgx.symm))
    obtain ⟨t, ht, he⟩ := htrans _ hgy hne
    obtain ⟨t, ht, rfl⟩ := ht
    exact ⟨t, hT.symm ▸ ht, he⟩
  obtain ⟨K, hKy, hodd, hK⟩ := Theory.GroupAction.exists_complement_fixing_point
    T (reduced_edge_solvable h hxm) y horbit
  have hKy' : K.map E.subtype ≤ stabilizer F y := by
    rintro a ⟨k, hk, rfl⟩
    exact hKy hk
  refine ⟨K, hT ▸ hK, hodd, hKy', ?_⟩
  apply (le_inf ?_ ?_).trans inf_normalizer_le_normalizer_inf
  · exact ((map_subtype_le K).trans inf_le_left).trans (stabilizer_normalizes_V F x 1)
  · exact hKy'.trans ((stabilizer F y).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F y))))

/-- The middle-core conjugator preserves the original two fixed vertices and intersection. -/
theorem source_middle_core_conjugate_complement (h : HypothesisF11 L S)
    {x m y z : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj y m)
    (hyz : (graph (reducedFamily L S)).Adj y z) (hzm : z ≠ m)
    (K : Subgroup (G₀ L S))
    (hKx : K ≤ stabilizer (reducedFamily L S) x)
    (hKm : K ≤ stabilizer (reducedFamily L S) m)
    (hKy : K ≤ stabilizer (reducedFamily L S) y)
    (hodd : Odd (Nat.card K))
    (htrans : ∀ w, (graph (reducedFamily L S)).Adj y w → w ≠ m →
      ∃ q ∈ Q (reducedFamily L S) m, q • z = w) :
    let F := reducedFamily L S
    let W := V F x 1 ⊓ Q F y
    ∃ q ∈ Q F m,
      K.map (MulAut.conj q).toMonoidHom ≤ stabilizer F x ⊓ stabilizer F y ⊓ stabilizer F z ∧
      K.map (MulAut.conj q).toMonoidHom ≤ normalizer (W : Set (G₀ L S)) ∧
      Nat.card (K.map (MulAut.conj q).toMonoidHom) = Nat.card K ∧
      (K.map (MulAut.conj q).toMonoidHom).map (G₀ L S).subtype =
        (K.map (G₀ L S).subtype).map (MulAut.conj (q : G)).toMonoidHom := by
  let F := reducedFamily L S
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let E := stabilizer F x ⊓ stabilizer F m
  let : Group.IsSolvable E := reduced_edge_solvable h hxm
  have hKE : K ≤ E := le_inf hKx hKm
  have hKsolv : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hKE) (inclusion_injective _)
  have hnorm : K ≤ normalizer (Q F m : Set (G₀ L S)) := hKm.trans
    ((stabilizer F m).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F m))))
  have hJm : Q F m ⊔ K ≤ stabilizer F m := sup_le (Q_le_stabilizer F m) hKm
  let : Finite (Q F m ⊔ K : Subgroup (G₀ L S)) :=
    Finite.of_injective (inclusion hJm) (inclusion_injective _)
  have horbit : ∀ k ∈ K, ∃ q ∈ Q F m, q • z = k • z := by
    intro k hk
    have hkfix : k • y = y := hKy hk
    have hkw : (graph F).Adj y (k • z) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F k).map_adj_iff.mpr hyz
      change (graph F).Adj (k • y) (k • z) at hh
      rwa [hkfix] at hh
    exact htrans _ hkw (fun he => hzm ((MulAction.injective k) (he.trans (hKm hk).symm)))
  obtain ⟨q, hq, hfix⟩ := Theory.GroupAction.exists_two_group_conjugate_fixing_point
    (Q F m) K (isPGroup_pCoreIn 2 _) hodd hKsolv hnorm z horbit
  have hQ := (source_Z_Q_U (reduced_triple h) m).2
  have hqx : q ∈ stabilizer F x :=
    ((hQ.trans (ballKernel_one_le_edge F hxm.symm)).trans inf_le_right) hq
  have hqy : q ∈ stabilizer F y :=
    ((hQ.trans (ballKernel_one_le_edge F hym.symm)).trans inf_le_right) hq
  have hconj (v : Vertex F) (hKv : K ≤ stabilizer F v) (hqv : q ∈ stabilizer F v) :
      K.map (MulAut.conj q).toMonoidHom ≤ stabilizer F v := by
    rintro a ⟨k, hk, rfl⟩
    exact (stabilizer F v).mul_mem ((stabilizer F v).mul_mem hqv (hKv hk))
      ((stabilizer F v).inv_mem hqv)
  have hKx' := hconj x hKx hqx
  have hKy' := hconj y hKy hqy
  refine ⟨q, hq, le_inf (le_inf hKx' hKy') hfix, ?_, ?_, ?_⟩
  · have hnQ : stabilizer F y ≤ normalizer (Q F y : Set (G₀ L S)) :=
      (stabilizer F y).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F y)))
    exact (le_inf (hKx'.trans (stabilizer_normalizes_V F x 1))
      (hKy'.trans hnQ)).trans inf_normalizer_le_normalizer_inf
  · exact (Nat.card_congr (K.equivMapOfInjective (MulAut.conj q).toMonoidHom
      (MulAut.conj q).injective).toEquiv).symm
  · rw [map_map, map_map]
    rfl

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
