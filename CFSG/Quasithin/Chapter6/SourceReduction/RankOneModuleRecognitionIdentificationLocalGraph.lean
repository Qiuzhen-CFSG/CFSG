module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalCoreGeometry
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Endpoints
public import Theory.GroupTheory.ReducedNormal.Equiv
/-!
# The actual coset graph in the contrary core branch

Construct the F.7 source setup for LT and an outside Sylow overgroup H inside
K = ⟨LT,H⟩. Uniqueness over LT makes K two-core-free, while the natural
centralizer identity makes the original layer reduced. All subgroup and Sylow
maps are the literal embeddings in K and the original ambient group.

The even critical pair of F.7.11 would be a noncommuting mutually normalizing
pair of layer conjugates, contradicting 6.2.3. Thus the critical distance is
odd. Contrary core containment makes it at least three, gives an elementary
H-conjugate closure and yields a normalized critical endpoint whose two
closure modules normalize each other. The minimal H-star vertex also has the
required unique maximal overgroup and generation parameter one.

This proves the first paragraph and the graph setup of 6.2.8. The field-plane
argument constructing its terminal non-two pair is still required; no core
exclusion or order-eight conclusion is asserted here.

Source: Aschbacher--Smith, 6.2.8, printed pp.684--685; F.7.6 and F.7.11,
printed pp.312--314. The Chapter 12 companion supplies uniqueness and the
normalizer factorization on [R₂(LT),L].
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterF.Section07.Track
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

private theorem natural_layer_centralizer (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n) :
    centralizer ((layer L R).subgroupOf (L ⊔ (T : Subgroup G)) : Set (L ⊔ (T : Subgroup G) : Subgroup G)) =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  apply map_injective (L ⊔ (T : Subgroup G)).subtype_injective
  rw [map_centralizer_subtype,
    map_subgroupOf_eq_of_le (h.layer_le_L.trans (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left))]
  exact local_layer_centralizer_eq_core h hnat

private theorem natural_layer_reduced (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n) :
    IsPReduced 2 ((layer L R).subgroupOf (L ⊔ (T : Subgroup G))) := by
  let X := L ⊔ (T : Subgroup G)
  let B := (layer L R).subgroupOf X
  have hBX : layer L R ≤ X := h.layer_le_L.trans le_sup_left
  have hn : X ≤ normalizer (layer L R : Set G) :=
    sup_le (by obtain ⟨F, _, _, _, _, hm⟩ := hnat; exact hm.normalizes)
      h.sylow_normalizes_layer
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  let := h.layer_elementary
  refine ⟨inferInstance, IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hBX).toMonoidHom (subgroupOfEquivOfLe hBX).injective, ?_⟩
  let q := QuotientGroup.quotientMulEquivOfEq (natural_layer_centralizer h hnat)
  apply (map_eq_bot_iff_of_injective _ (f := q.toMonoidHom) q.injective).mp
  rw [pCore_map_iso]
  exact pCore_quotient_pCore_eq_bot 2

/-- F.7.6 for the literal pair LT,H inside its generated subgroup. -/
theorem local_graph_setup (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M)
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H) (hHM : ¬ H ≤ M) :
    let X := L ⊔ (T : Subgroup G)
    let K := X ⊔ H
    let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K else X.subgroupOf K
    ∃ D : SourceSetup F, D.V ≠ ⊥ ∧
      D.seed.map K.subtype = layer L R ∧
      (D.sylow false : Subgroup (F false)).map
        (K.subtype.comp (F false).subtype) = (T : Subgroup G) := by
  let X := L ⊔ (T : Subgroup G)
  let K := X ⊔ H
  let A := X.subgroupOf K
  let B := H.subgroupOf K
  let F : Bool → Subgroup K := fun i => if i then B else A
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTK : (T : Subgroup G) ≤ K := hTX.trans le_sup_left
  let S := T.subtype hTK
  have hSA : (S : Subgroup K) ≤ A := fun x hx => hTX hx
  have hSB : (S : Subgroup K) ≤ B := fun x hx => hTH hx
  let P : ∀ i, Sylow 2 (F i) := fun i => S.subtype (by
    cases i
    · exact hSA
    · exact hSB)
  let eA : A ≃* X := subgroupOfEquivOfLe (show X ≤ K from le_sup_left)
  let V0 := (layer L R).subgroupOf X
  let V1 := V0.map eA.symm.toMonoidHom
  have hr : IsPReduced 2 V1 := (natural_layer_reduced h hnat).map_equiv eA.symm
  have hfitX : generalizedFitting X = pCore 2 X :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp
      (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
        ⟨h.local_mem.1.prop.2.2, hTX⟩))
  have hfitA : generalizedFitting A = pCore 2 A := by
    apply map_injective (f := eA.toMonoidHom) eA.injective
    rw [map_generalizedFitting_equiv, pCore_map_iso, hfitX]
  have hcA : centralizer (V1 : Set A) = pCore 2 A := by
    have hh := congrArg (Subgroup.map eA.symm.toMonoidHom)
      (natural_layer_centralizer h hnat)
    rw [pCore_map_iso] at hh
    rw [← hh]
    simpa only [V1, V0, coe_map, ← MulEquiv.toMonoidHom_eq_coe, MulEquiv.coe_toMonoidHom]
      using (map_centralizer_equiv (V0 : Set X) eA.symm).symm
  have hg : F false ⊔ F true = ⊤ := by
    change A ⊔ B = ⊤
    apply map_injective K.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show X ≤ K from le_sup_left),
      map_subgroupOf_eq_of_le (show H ≤ K from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hcore : pCore 2 K = ⊥ :=
    twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup X H M hunique hHM
  let D : SourceSetup F := {
    finite := fun _ => inferInstance
    generates := hg
    characteristicTwo := hfitA
    core_free := by
      let d : (F false ⊔ F true : Subgroup K) ≃* K :=
        (MulEquiv.subgroupCongr hg).trans topEquiv
      apply (map_eq_bot_iff_of_injective _ (f := d.toMonoidHom) d.injective).mp
      rw [pCore_map_iso]
      exact hcore
    sylow := P
    same_sylow := (map_subgroupOf_eq_of_le hSA).trans
      (map_subgroupOf_eq_of_le hSB).symm
    V := V1
    reduced := hr
    centralizer_eq := by
      rw [AmalgamLocalCores.reduced_centralizer_core _ hr, hcA]
      exact inf_eq_right.mpr (pCore_isPGroup.le_sylow_of_normal (P false)) }
  have hseed : D.seed.map K.subtype = layer L R := by
    change ((V0.map eA.symm.toMonoidHom).map A.subtype).map K.subtype = _
    rw [map_map, map_map]
    have he : (K.subtype.comp A.subtype).comp eA.symm.toMonoidHom = X.subtype := rfl
    rw [he]
    exact map_subgroupOf_eq_of_le (h.layer_le_L.trans le_sup_left)
  refine ⟨D, ?_, hseed, ?_⟩
  · intro hz
    have he : D.seed.map K.subtype = ⊥ := by simp only [SourceSetup.seed, hz, Subgroup.map_bot]
    exact h.nontrivial_action (hseed.symm.trans he)
  · rw [← map_map]
    change (((S.subtype hSA : Sylow 2 A) : Subgroup A).map A.subtype).map K.subtype = _
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hSA]
    change ((T.subtype hTK : Sylow 2 K) : Subgroup K).map K.subtype = _
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTK]

open Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Section07.CriticalPairs

/-- The critical distance in the original LT,H graph is odd, by 6.2.3
and the actual even critical pair of F.7.11(2). -/
theorem local_graph_track_odd (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    {H : Subgroup G}
    (D : SourceSetup (fun i => if i then H.subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H)
      else (L ⊔ (T : Subgroup G)).subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H)))
    (hne : D.V ≠ ⊥)
    (hseed : D.seed.map ((L ⊔ (T : Subgroup G)) ⊔ H).subtype = layer L R) :
    Odd (D.track hne) := by
  let K := (L ⊔ (T : Subgroup G)) ⊔ H
  let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
    else (L ⊔ (T : Subgroup G)).subgroupOf K
  apply (Nat.even_or_odd _).resolve_left
  intro heven
  obtain ⟨v, hd, hcrit⟩ := (D.critical_witness hne).1
  have hv := even_endpoint_type F D hne hd heven
  have hp := SourceAction.even_critical_pair D hne hd heven hcrit
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  rw [vertexModule_first F D.seed hv, ← hg,
    firstModule_translate_base F D.seed D.seed_normalized] at hp
  have hconj : (D.seed.map (MulAut.conj g).toMonoidHom).map K.subtype =
      (layer L R).map (MulAut.conj (g : G)).toMonoidHom := by
    rw [map_map]
    have he : K.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp K.subtype := rfl
    rw [he, ← map_map, hseed]
  have hbound := map_mono (f := K.subtype) hp.2.1
  rw [map_commutator, map_inf _ _ _ K.subtype_injective, hseed, hconj] at hbound
  have hc := local_commuting_normalized h hnatural hE hfactor (g : G)
    (le_normalizer_iff_commutator_le_right.mpr (hbound.trans inf_le_right))
    (le_normalizer_iff_commutator_le_left.mpr (hbound.trans inf_le_left))
  apply hp.1
  apply (map_eq_bot_iff_of_injective _ K.subtype_injective).mp
  rwa [map_commutator, hseed, hconj]

/-- In the contrary branch of 6.2.8 the actual H-conjugate closure of V is
an elementary abelian subgroup of O₂(H). This uses the odd coset distance,
not a commutativity premise on the closure. -/
theorem local_graph_closure_elementary (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M)
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H) (hHM : ¬ H ≤ M)
    (hcore : layer L R ≤ H.pCoreIn 2) :
    IsElementaryAbelian 2 (⨆ g : H,
      (layer L R).map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) := by
  let K := (L ⊔ (T : Subgroup G)) ⊔ H
  let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
    else (L ⊔ (T : Subgroup G)).subgroupOf K
  obtain ⟨D, hne, hseed, _⟩ := local_graph_setup h
    (hnatural.1 ▸ hnatural.2.1) hunique hTH hHM
  have hodd := local_graph_track_odd h hnatural hE hfactor D hne hseed
  have htrue : (F true).map K.subtype = H := map_subgroupOf_eq_of_le le_sup_right
  have hcore' : D.seed ≤ (F true).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective K.subtype_injective).mp
    rw [map_pCoreIn_of_injective 2 _ _ K.subtype_injective, htrue, hseed]
    exact hcore
  let J := ⨆ g : F true, D.seed.map (MulAut.conj (g : K)).toMonoidHom
  let := Completion.conjugate_join_elementary_of_odd F D hne hcore' hodd
  have he : J.map K.subtype = ⨆ g : H,
      (layer L R).map (MulAut.conj (g : G)).toMonoidHom := by
    rw [show J = ⨆ g : F true, D.seed.map (MulAut.conj (g : K)).toMonoidHom from rfl,
      Subgroup.map_iSup]
    have hc (g : K) : (D.seed.map (MulAut.conj g).toMonoidHom).map K.subtype =
        (layer L R).map (MulAut.conj (g : G)).toMonoidHom := by
      rw [map_map]
      have hm : K.subtype.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj (g : G)).toMonoidHom.comp K.subtype := rfl
      rw [hm, ← map_map, hseed]
    apply le_antisymm
    · apply iSup_le
      intro g
      rw [hc]
      exact le_iSup_of_le (⟨g.val.val, g.property⟩ : H) le_rfl
    · apply iSup_le
      intro g
      let g' : F true := ⟨⟨g.val, (show H ≤ K from le_sup_right) g.property⟩, g.property⟩
      exact le_iSup_of_le g' (by rw [hc])
  rw [← he]
  exact IsElementaryAbelian.map K.subtype

/-- The first paragraph of 6.2.8 on the actual generated group: the contrary
core inclusion gives odd critical distance at least three and a normalized
critical endpoint whose two closure modules normalize one another. -/
theorem local_graph_contrary_configuration
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M)
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H) (hHM : ¬ H ≤ M)
    (hcore : layer L R ≤ H.pCoreIn 2) :
    let K := (L ⊔ (T : Subgroup G)) ⊔ H
    let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
      else (L ⊔ (T : Subgroup G)).subgroupOf K
    ∃ (D : SourceSetup F) (hne : D.V ≠ ⊥),
      D.seed.map K.subtype = layer L R ∧
      Odd (D.track hne) ∧ 3 ≤ D.track hne ∧
      ∃ e : NormalizedEndpoint D hne,
        ⁅vertexModule F D.seed (base F true), vertexModule F D.seed e.vertex⁆ ≤
          vertexModule F D.seed (base F true) ⊓ vertexModule F D.seed e.vertex := by
  let K := (L ⊔ (T : Subgroup G)) ⊔ H
  let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
    else (L ⊔ (T : Subgroup G)).subgroupOf K
  obtain ⟨D, hne, hseed, _⟩ := local_graph_setup h
    (hnatural.1 ▸ hnatural.2.1) hunique hTH hHM
  have hodd := local_graph_track_odd h hnatural hE hfactor D hne hseed
  have htrue : (F true).map K.subtype = H := map_subgroupOf_eq_of_le le_sup_right
  have hcore' : D.seed ≤ (F true).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective K.subtype_injective).mp
    rw [map_pCoreIn_of_injective 2 _ _ K.subtype_injective, htrue, hseed]
    exact hcore
  have hb1 := Completion.one_lt_track_of_true_core F D hne hcore'
  have hb : 3 ≤ D.track hne := by
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨e⟩ := NormalizedEndpoint.nonempty (D := D) (hne := hne) hodd
  exact ⟨D, hne, hseed, hodd, hb, e, e.commutator_le hb⟩

/-- The minimal H-star vertex in the escaping centralizer satisfies the
source normalizer and unique-maximal conditions. Its layer closure is
actually elementary abelian in the contrary core branch. -/
theorem local_exists_contrary_graph_vertex
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M)
    {z : G} (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hescape : ¬ centralizer ({z} : Set G) ≤ M)
    (hcore : layer L R ≤ (centralizer ({z} : Set G)).pCoreIn 2) :
    ∃ H ∈ Chapter3.HStar (T : Subgroup G) M,
      H ≤ centralizer ({z} : Set G) ∧ ChapterE.generationParameter H = 1 ∧
      H ⊓ normalizer (layer L R : Set G) = H ⊓ M ∧
      H ⊓ M ⋖ H ∧
      (∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ⋖ H → X = H ⊓ M) ∧
      layer L R ≤ H.pCoreIn 2 ∧
      IsElementaryAbelian 2 (⨆ g : H,
        (layer L R).map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) := by
  obtain ⟨H, hH, hHz, hn, _, hmax, huniq⟩ :=
    local_exists_hstar_in_centralizer h ho hT hescape
  have hVH : layer L R ≤ H.pCoreIn 2 := hcore.trans
    (Chapter3.twoCore_le_of_sylow_le T hH.1.1.2 hHz)
  have hnorm : H ⊓ normalizer (layer L R : Set G) = H ⊓ M := by
    apply le_antisymm (inf_le_inf_left _ hE.normalizer_le)
    intro x hx
    have he := local_layer_normalizer hE hz ho
    exact ⟨hx.1, ((he.symm.le) ⟨hHz hx.1, hx.2⟩).2⟩
  exact ⟨H, hH, hHz, hn, hnorm, hmax, huniq, hVH,
    local_graph_closure_elementary h hnatural hE hfactor hunique hH.1.1.2 hH.1.2 hVH⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
