module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborSylow
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LocalGeneration
public import Theory.SpecificGroups.SL2.NormalizerInvariantClosure

/-!
# The original normal closure in DGS 9.4

For adjacent alpha and beta, W is the closure of Q_alpha under the full
G_beta. The beta linear marking makes W surject onto the local quotient.
Removing the Sylow supplement identifies W with O²(L_beta) Q_alpha and
identifies Z_alpha intersect Z(W) with its residual centralizer.

The genuine 6.5 obstruction makes W intersect Q_beta escape Q_alpha.
Its image in the alpha edge Sylow is nonzero and normalizer invariant.
Rank-one omega fusion then puts the entire quotient omega-center preimage
in W, including the small Suzuki and unitary catalogue rows. The actual
full-edge Sylow, quotient map, and relative normal closure are retained.
The earlier alpha catalogue and 6.5 input remain explicit.
Source: DGS, Groups and Graphs (1985), 9.4, especially (iii), printed p.143.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem normalClosure_eq_residual_sup_of_normalized_sylow
    {H : Type*} [Group H] [Finite H] (A : Subgroup H) (T : Sylow 2 H)
    (hn : (T : Subgroup H) ≤ normalizer (A : Set H))
    (hr : pResidual 2 H ≤ normalClosure (A : Set H)) :
    normalClosure (A : Set H) = pResidual 2 H ⊔ A := by
  apply le_antisymm ?_ (sup_le hr le_normalClosure)
  rw [normalClosure_eq_conjugateSpanBy_top,←pResidual_sup_sylow_eq_top T,
    conjugateSpanBy_sup_of_normalizes_seed A (pResidual 2 H) T hn le_normalizer_of_normal]
  exact conjugateSpanBy_le le_sup_right (le_sup_left.trans (pResidual 2 H ⊔ A).le_normalizer)

/-- The source normal closure under the full vertex stabilizer is the beta
residual joined with the original alpha core. -/
theorem neighbor_core_closure_eq_residual_sup
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hne : ¬ Q (family P) w ≤ Q (family P) v)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    let H := graphLocalGroup (family P) v
    conjugateSpanBy (Q (family P) w) (stabilizer (family P) v) =
      (pResidual 2 H).map H.subtype ⊔ Q (family P) w := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ v
  let A := (Q Γ w).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hAH := neighbor_core_le_localGroup h hB hS hvw
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hp : IsPGroup 2 q.ker := hk.symm ▸ pCore_isPGroup
  obtain ⟨T,hT,hTf⟩ := linear_neighbor_core_sylow_image h hB hS hvw hne e
  let S : Sylow 2 H := T.comapOfKerIsPGroup q hp
    (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top)
  let X := normalClosure (A : Set H)
  have hn : (S : Subgroup H) ≤ normalizer (A : Set H) := by
    intro l hl
    apply le_normalizer_comap H.subtype
    exact stabilizer_normalizes_Q Γ w ((hTf l).mp
      ((T : Subgroup SL(2,F)).le_normalizer hl))
  have hm : X.map q = ⊤ := by
    let : (X.map q).Normal := (inferInstance : X.Normal).map q hq
    obtain ⟨g,_,hg⟩ := Matrix.SpecialLinearGroup.exists_residual_conjugate_sylow_image_sup_eq_top
      T (MonoidHom.id SL(2,F)) Function.surjective_id
    simp only [Subgroup.map_id] at hg
    have hTX : (T : Subgroup SL(2,F)) ≤ X.map q := hT ▸ map_mono (show A ≤ X from le_normalClosure)
    apply top_unique
    rw [←hg]
    refine sup_le hTX ?_
    rintro _ ⟨x,hx,rfl⟩
    exact (inferInstance : (X.map q).Normal).conj_mem x (hTX hx) g
  have hsup : X ⊔ q.ker = ⊤ := by
    simpa only [comap_map_eq,comap_top] using congrArg (Subgroup.comap q) hm
  have hr : pResidual 2 H ≤ X :=
    sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top X q.ker hp hsup⟩
  have hx := congrArg (Subgroup.map H.subtype)
    (normalClosure_eq_residual_sup_of_normalized_sylow A S hn hr)
  rw [map_normalClosure_eq_conjugateSpanBy_range,map_subgroupOf_eq_of_le hAH,
    range_subtype,Subgroup.map_sup,map_subgroupOf_eq_of_le hAH] at hx
  rw [←graphLocalGroup_sup_edge h hB hS hvw]
  rw [conjugateSpanBy_sup_of_normalizes_seed _ H _
    (inf_le_right.trans (stabilizer_normalizes_Q Γ w))
    (inf_le_left.trans (sylowGenerated_normalized _))]
  exact hx

/-- The center kernel in the source normal closure is exactly the residual
centralizer used by the original natural section. -/
theorem neighbor_core_closure_center_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hne : ¬ Q (family P) w ≤ Q (family P) v)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    let H := graphLocalGroup (family P) v
    let W := conjugateSpanBy (Q (family P) w) (stabilizer (family P) v)
    Z (family P) w ⊓ (Subgroup.center W).map W.subtype =
      Z (family P) w ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G) := by
  let Γ := family P
  let H := graphLocalGroup Γ v
  let W := conjugateSpanBy (Q Γ w) (stabilizer Γ v)
  have he := neighbor_core_closure_eq_residual_sup h hB hS hvw hne e
  change W = (pResidual 2 H).map H.subtype ⊔ Q Γ w at he
  have hZW : Z Γ w ≤ W := ((source_Z_Q_U h w).1.trans
    (fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz).1)).trans (le_conjugateSpanBy _ _)
  have hfix := CommutingNontrivial.Z_centralizes_Q Γ w (source_Z_Q_U h w).1
  have hcenter : (Subgroup.center W).map W.subtype = W ⊓ centralizer (W : Set G) := by
    ext x
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨x.property,?_⟩
      intro y hy
      exact congrArg Subtype.val ((mem_center_iff.mp hx) ⟨y,hy⟩)
    · rintro ⟨hx,hc⟩
      refine ⟨⟨x,hx⟩,?_,rfl⟩
      exact mem_center_iff.mpr (fun y => Subtype.ext (hc y y.property))
  change Z Γ w ⊓ (Subgroup.center W).map W.subtype =
    Z Γ w ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G)
  rw [hcenter,←inf_assoc,inf_eq_left.mpr hZW,he]
  apply le_antisymm (inf_le_inf_left _ (centralizer_le (show (pResidual 2 H).map H.subtype ≤
    (pResidual 2 H).map H.subtype ⊔ Q Γ w from le_sup_left)))
  rintro z ⟨hz,hr⟩
  refine ⟨hz,?_⟩
  have hc : (pResidual 2 H).map H.subtype ⊔ Q Γ w ≤ centralizer ({z} : Set G) := by
    apply sup_le
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (hr x hx)
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (hfix hz x hx)
  intro x hx
  exact mem_centralizer_singleton_iff.mp (hc hx)


/-- Source 6.5 forces the normal closure to have a larger intersection with
the edge Sylow than the original neighboring core. Already its intersection
with the beta core escapes the alpha core. -/
theorem neighbor_core_closure_inter_core_escape
    (Γ : Bool → Subgroup G) {v w : Vertex Γ}
    (hob : ¬ stabilizer Γ v ≤ normalizer ((Q Γ w ⊓ Q Γ v : Subgroup G) : Set G)) :
    ¬ conjugateSpanBy (Q Γ w) (stabilizer Γ v) ⊓ Q Γ v ≤ Q Γ w := by
  intro hle
  let W := conjugateSpanBy (Q Γ w) (stabilizer Γ v)
  have he : W ⊓ Q Γ v = Q Γ w ⊓ Q Γ v :=
    le_antisymm (le_inf hle inf_le_right) (inf_le_inf_right _ (le_conjugateSpanBy _ _))
  apply hob
  rw [←he]
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy (Q Γ w) (stabilizer Γ v) hg),
    mem_normalizer_iff_map_conj_eq.mp (stabilizer_normalizes_Q Γ v hg)]


private theorem rank_one_omega_le_normalized
    {D : Type*} [Group D] [Finite D] (M : IsRankOneModel D) (S : Sylow 2 D)
    (A : Subgroup D) (hAS : A ≤ S) (hne : A ≠ ⊥)
    (hn : normalizer (S : Set D) ≤ normalizer (A : Set D)) :
    omegaCenterIn (S : Subgroup D) ≤ A := by
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hne
  have hp : IsPGroup 2 A := S.isPGroup'.to_le hAS
  obtain ⟨n,hnpos,hcard⟩ := hp.nontrivial_iff_card.mp inferInstance
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 2
    (by rw [hcard]; exact dvd_pow_self 2 (by omega))
  have hx2 : (x : D)^2 = 1 := congrArg Subtype.val (show x^2 = 1 from hx ▸ pow_orderOf_eq_one x)
  have hxne : (x : D) ≠ 1 := by
    intro he
    have hx1 : x = 1 := Subtype.ext he
    simp only [hx1,orderOf_one] at hx
    omega
  let E := zpowers (x : D)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.zpowers_of_pow_eq_one hx2
  have hEA : E ≤ A := zpowers_le.mpr x.property
  have hE : E ≠ ⊥ := by
    intro he
    have hxE : (x : D) ∈ E := mem_zpowers _
    rw [he,mem_bot] at hxE
    exact hxne hxE
  rw [←CommutingNontrivial.source_rank_one_omega_generated M S E (hEA.trans hAS) hE]
  exact conjugateSpanBy_le hEA hn

/-- A normalized subgroup of an original Sylow which contains the quotient
kernel and escapes it contains the full preimage of the quotient omega-center. -/
private theorem rank_one_omega_preimage_le
    {H : Type*} [Group H] [Finite H]
    (M : IsRankOneModel (H ⧸ pCore 2 H)) (S : Sylow 2 H)
    (A : Subgroup H) (hAS : A ≤ S) (hQA : pCore 2 H ≤ A)
    (hne : ¬ A ≤ pCore 2 H)
    (hn : normalizer (S : Set H) ≤ normalizer (A : Set H)) :
    (omegaCenterIn ((S : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)))).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ A := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hq := QuotientGroup.mk'_surjective (pCore 2 H)
  let T : Sylow 2 (H ⧸ pCore 2 H) := S.mapSurjective (f := q) hq
  have hne' : A.map q ≠ ⊥ := by
    intro he
    have hh := (map_eq_bot_iff A).mp he
    rw [QuotientGroup.ker_mk'] at hh
    exact hne hh
  have hn' : normalizer (T : Set (H ⧸ pCore 2 H)) ≤ normalizer (A.map q : Set _) := by
    change normalizer (↑((S : Subgroup H).map q) : Set (H ⧸ pCore 2 H)) ≤ _
    rw [←S.normalizer_map_surjective q hq]
    exact (map_mono hn).trans (le_normalizer_map q)
  have hh := comap_mono (f := q) (rank_one_omega_le_normalized M T (A.map q) (map_mono hAS) hne' hn')
  simpa only [comap_map_eq,T,Sylow.coe_mapSurjective,q,QuotientGroup.ker_mk',sup_eq_left.mpr hQA] using hh


/-- The full preimage of the alpha quotient Sylow omega-center lies in the
normal closure W from 9.4, with the original full-edge Sylow retained. -/
theorem reduced_neighbor_core_closure_omega_preimage (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {a beta : Vertex (Reduction.reducedFamily L S₀)}
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (M : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a))) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    let W := conjugateSpanBy (Q Γ a) (stabilizer Γ beta)
    ∃ R : Sylow 2 H,
      (R : Subgroup H).map H.subtype = (stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2 ∧
      ((omegaCenterIn ((R : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)))).comap
        (QuotientGroup.mk' (pCore 2 H))).map H.subtype ≤ W := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a
  let W := conjugateSpanBy (Q Γ a) (stabilizer Γ beta)
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨R,hR⟩ := CommutingNontrivial.source_edge_core_local_sylow ht
    (Reduction.reduced_borel_core_sylow h) d hab
  change Sylow 2 H at R
  change (R : Subgroup H).map H.subtype = (stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2 at hR
  let A := W.subgroupOf H ⊓ (R : Subgroup H)
  have hQA : pCore 2 H ≤ A := by
    apply le_inf ?_ (pCore_isPGroup.le_sylow_of_normal R)
    intro x hx
    exact le_conjugateSpanBy _ _ ((graphLocalGroup_core ht a) ▸ mem_map_of_mem H.subtype hx)
  have hQB : Q Γ beta ≤ (R : Subgroup H).map H.subtype := by
    rw [hR]
    have hh : Q Γ beta ≤ (stabilizer Γ beta ⊓ stabilizer Γ a).pCoreIn 2 :=
      Noncommuting.graph_Q_le_edgeCore ht hab.symm
    rwa [inf_comm] at hh
  have hne : ¬ A ≤ pCore 2 H := by
    intro hle
    apply neighbor_core_closure_inter_core_escape Γ (hob beta a hab.symm)
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hQB hx.2
    have hm := hle (show y ∈ A from ⟨hx.1,hy⟩)
    exact (graphLocalGroup_core ht a) ▸ mem_map_of_mem H.subtype hm
  have hn : normalizer (R : Set H) ≤ normalizer (A : Set H) := by
    intro g hg
    have hgb : (g : Reduction.G₀ L S₀) ∈ stabilizer Γ beta := by
      have he := (CommutingNontrivial.source_edge_local_normalizer ht d hab M R hR).2
      exact (show g ∈ (stabilizer Γ beta).subgroupOf H from he.symm ▸ hg)
    have hgW : g ∈ normalizer (W.subgroupOf H : Set H) := le_normalizer_comap H.subtype
      (le_normalizer_conjugateSpanBy (Q Γ a) (stabilizer Γ beta) hgb)
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      mem_normalizer_iff_map_conj_eq.mp hgW,mem_normalizer_iff_map_conj_eq.mp hg]
  have hle := rank_one_omega_preimage_le M R A inf_le_right hQA hne hn
  refine ⟨R,hR,?_⟩
  rintro x ⟨y,hy,rfl⟩
  exact (hle hy).1



end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
