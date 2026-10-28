module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicSylowSeparation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveGraphCatalogue
public import Theory.SpecificGroups.GL2.ThreeSylowNormalElementary
public import Theory.Frattini.SquareImage
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LocalGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicEdgeGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SeedEscape

/-!
# Intrinsic critical-center and seed geometry at distance one

A nonzero elementary subgroup normal in a local Sylow determines that Sylow
in every original quotient, including the order-144 enlargement. In that
exceptional quotient the normal elementary image lies in Frattini, hence in
the normal PSU₃(2) subgroup of index two. Its involution determines the Sylow
of that subgroup; self-normalization then determines the ambient Sylow.

Apply this to the actual critical center, which is normalized by its edge
radical. Its unique fixed neighbor proves that two distinct neighboring
critical centers cannot generate a two-group. The original displacement
argument gives (11.2)(c), while Sylow conjugacy inside the center pair gives
its neighbor conjugator and the mixed intersections of (11.3)(a).
Neither endpoint catalogue is an input. This does not yet identify the full
pair-core quotient or exclude every occurrence of the order-144 enlargement.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.1), pp.104--105, (11.2)(c) and (11.3)(a), pp.168--169; the exceptional
Sylow calculation is ThreeSylowNormalElementary's checked SD16 argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P B : Subgroup G}

private theorem sylow_eq_of_nontrivial_intersection_with_projective
    {D : Type*} [Group D] [Finite D] (I : Subgroup D) [I.Normal]
    (hm : ClassicalGroup.IsPSU I 3 2) (hi : I.index ≤ 2)
    (hc : pCore 2 D = ⊥) (R T : Sylow 2 D)
    (A : Subgroup D) [IsElementaryAbelian 2 A]
    (hAR : A ≤ R) (hAT : A ≤ T) (hAI : A ≤ I) (hne : A ≠ ⊥) : R = T := by
  have hq : IsPGroup 2 (D ⧸ I) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    change I.index ∣ 2^1
    have hn := I.index_ne_zero_of_finite
    have he : I.index = 1 ∨ I.index = 2 := by omega
    rcases he with he | he <;> simp [he]
  have hIcore : pCore 2 I = ⊥ := by
    rw [pCore_eq_comap_of_normal,hc]
    exact (MonoidHom.ker_eq_bot_iff I.subtype).mpr I.subtype_injective
  obtain ⟨U,hU⟩ := R.exists_subgroupOf_eq_of_normal I
  obtain ⟨V,hV⟩ := T.exists_subgroupOf_eq_of_normal I
  obtain ⟨x,hx,hx1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have hUV : U = V := source_rank_one_sylow_eq_of_common_involution
    (.projective_unitary 1 (by decide) (by simpa using hm)) hIcore U V ⟨x,hAI hx⟩
    (by change (⟨x,hAI hx⟩ : I) ∈ (U : Subgroup I); rw [show (U : Subgroup I) = (R : Subgroup D).subgroupOf I from hU]; exact hAR hx)
    (by change (⟨x,hAI hx⟩ : I) ∈ (V : Subgroup I); rw [show (V : Subgroup I) = (T : Subgroup D).subgroupOf I from hV]; exact hAT hx)
    (fun he => hx1 (congrArg Subtype.val he))
    (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx))
  apply Sylow.eq_of_restriction_of_normal_self_normalizing I hq
    (isPSU_two_sylow_normalizer_eq hm) R T
  have hh := congrArg (fun S : Sylow 2 I => (S : Subgroup I).map I.subtype) hUV
  rwa [hU,hV,subgroupOf_map_subtype,subgroupOf_map_subtype] at hh

private theorem normal_elementary_le_index_two
    {D : Type*} [Group D] [Finite D] (I : Subgroup D) [I.Normal]
    (hi : I.index ≤ 2) (hD : Nat.card D = 144)
    (N : Subgroup D) [N.Normal] [IsElementaryAbelian 3 N]
    (hN : Nat.card N = 9) (hc : pCore 2 D = ⊥)
    (R : Sylow 2 D) (A : Subgroup D) [IsElementaryAbelian 2 A]
    (hAR : A ≤ R) (hn : (R : Subgroup D) ≤ normalizer (A : Set D)) : A ≤ I := by
  let E := A.subgroupOf (R : Subgroup D)
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer hAR).mpr hn
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hAR
  have hE := normal_elementary_le_frattini_of_normal_nine hD N hN hc R E
  let f : R →* D ⧸ I := (QuotientGroup.mk' I).comp (R : Subgroup D).subtype
  have hi2 : I.index ∣ 2 := by
    have hpos := I.index_ne_zero_of_finite
    have he : I.index = 1 ∨ I.index = 2 := by omega
    rcases he with he | he <;> simp [he]
  have hphi := frattini_le_ker_of_square_image f (fun x => by
    apply orderOf_dvd_iff_pow_eq_one.mp
    exact (orderOf_dvd_natCard (f x)).trans hi2)
  intro x hx
  exact (QuotientGroup.eq_one_iff _).mp (hphi (hE (show (⟨x,hAR hx⟩ : R) ∈ E from hx)))

/-- An elementary subgroup normal in one local Sylow determines that Sylow,
including the exceptional order-144 projective enlargement. -/
theorem localEnlargement_normal_elementary_sylow_unique
    (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (R T : Sylow 2 (localEnlargement d ⧸ pCore 2 (localEnlargement d)))
    (A : Subgroup (localEnlargement d ⧸ pCore 2 (localEnlargement d)))
    [IsElementaryAbelian 2 A] (hAR : A ≤ R) (hAT : A ≤ T)
    (hn : (R : Subgroup (localEnlargement d ⧸ pCore 2 (localEnlargement d))) ≤ normalizer (A : Set (localEnlargement d ⧸ pCore 2 (localEnlargement d)))) (hne : A ≠ ⊥) : R = T := by
  let := d.finite_P
  let M := localEnlargement d
  let : Finite M := Finite.of_injective (inclusion (localEnlargement_le d)) (inclusion_injective _)
  have rankOne (hm : IsRankOneModel (M ⧸ pCore 2 M)) : R = T := by
    obtain ⟨x,hx,hx1⟩ := A.bot_or_exists_ne_one.resolve_left hne
    exact source_rank_one_sylow_eq_of_common_involution hm (pCore_quotient_pCore_eq_bot 2)
      R T x (hAR hx) (hAT hx) hx1 (elemPow_eq_one_of_isElementaryAbelian x hx)
  rcases localEnlargement_rankOne_or_small_unitary d hB with hm | hp | hs
  · exact rankOne hm
  · have hpmark := hp
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hp
    let := hF
    let := hfin
    rcases localEnlargement_small_projective_alternatives d hB J hcard hconj e with he | he
    · let f := MulEquiv.subgroupCongr he
      apply rankOne
      exact (IsRankOneModel.projective_unitary 1 (by decide) (by simpa using hpmark)).of_equiv
        (QuotientGroup.congr _ _ f (pCore_map_iso 2 f))
    · let D := M ⧸ pCore 2 M
      let C := d.Pstar.subgroupOf M
      let q := QuotientGroup.mk' (pCore 2 M)
      let I := C.map q
      let : C.Normal := normal_subgroupOf_of_le_normalizer ((localEnlargement_le d).trans
        ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal))
      let : I.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
      let f : C ≃* d.Pstar := subgroupOfEquivOfLe le_sup_left
      let g := (coreQuotientEquivImage 2 C).symm.trans
        ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e)
      have hI : Nat.card I = 72 := (Nat.card_congr g.toEquiv).trans
        (BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwo.card_projective J hcard hconj)
      have hi : I.index ≤ 2 := by
        have hh := I.card_mul_index
        rw [hI,he] at hh
        omega
      obtain ⟨N,hN,hE,h9⟩ := localEnlargement_projective_normal_nine d hpmark
      let := hN
      let := hE
      have hAI := normal_elementary_le_index_two I hi he N h9
        (pCore_quotient_pCore_eq_bot 2) R A hAR hn
      exact sylow_eq_of_nontrivial_intersection_with_projective I
        ⟨F,inferInstance,inferInstance,J,hcard,hconj,⟨g⟩⟩ hi
        (pCore_quotient_pCore_eq_bot 2) R T A hAR hAT hAI hne
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hs
    let := hF
    let := hfin
    have he := localEnlargement_eq_star_of_small_special d hB J hcard hconj e
    let f := MulEquiv.subgroupCongr he
    exact rankOne (d.quotient.of_equiv (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)))


private theorem pGroup_fixes_neighbor {P : Fin 2 → Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (A : Subgroup G) (hp : IsPGroup 2 A) (hAb : A ≤ stabilizer (family P) b) :
    ∃ w, (graph (family P)).Adj b w ∧ A ≤ stabilizer (family P) w := by
  let := finite_endpoints h
  let L := d.localGroup b
  let : Finite L := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  have hAL : A ≤ L := pGroup_le_localGroup (family P) d b A hp hAb
  obtain ⟨R,hR⟩ := hp.comap_subtype (K := L) |>.exists_le_sylow
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab.symm
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq L T R
  have hfix : (R : Subgroup L).map L.subtype ≤ stabilizer (family P) ((g : G) • a) := by
    rw [←hg]
    change ((T : Subgroup L).map (MulAut.conj g).toMonoidHom).map L.subtype ≤ _
    rw [map_map]
    have he : L.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp L.subtype := by ext x; rfl
    rw [he,←map_map,hT,stabilizer_translate]
    exact map_mono ((pCoreIn_le 2 _).trans inf_le_right)
  refine ⟨(g : G) • a,?_,?_⟩
  · have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) (g : G)).map_adj_iff.mpr hab.symm
    change (graph (family P)).Adj ((g : G) • b) ((g : G) • a) at hh
    rwa [show (g : G) • b = b from d.local_le b g.property] at hh
  · intro x hx
    exact hfix (mem_map_of_mem L.subtype (hR (show (⟨x,hAL hx⟩ : L) ∈ A.subgroupOf L from hx)))

open DGS85.Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem original_enlarged_normal_elementary_sylow_unique
    (h : HypothesisF11 L S) (i : Fin 2)
    (R T : Sylow 2 (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)))
    (A : Subgroup (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)))
    [IsElementaryAbelian 2 A] (hAR : A ≤ R) (hAT : A ≤ T)
    (hn : (R : Subgroup (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i))) ≤ normalizer (A : Set (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)))) (hne : A ≠ ⊥) : R = T := by
  let hh := SuzukiContainment.reduced_hypothesis h
  have hB : ∃ T : Sylow 2 (commonBorel L (SuzukiContainment.reducedSylow L S)),
      (T : Subgroup _) = pCore 2 (commonBorel L (SuzukiContainment.reducedSylow L S)) := by
    apply f11_borel_core_sylow hh
    exact (normal_subgroupOf_iff_le_normalizer
      (show SuzukiContainment.reducedSylow L S ≤ commonBorel L (SuzukiContainment.reducedSylow L S)
        from le_sup_right)).mp (SuzukiContainment.reduced_sylow_normal h)
  have hs := localEnlargement_normal_elementary_sylow_unique (hh.starredLocalRankOneData i) hB
  rw [reduced_localEnlargement_eq h i] at hs
  exact hs R T A hAR hAT hn hne

private theorem marked_enlarged_normal_elementary_sylow_unique
    (h : HypothesisF11 L S) (i : Fin 2) {D : Type*} [Group D] [Finite D]
    (e : D ≃* (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)))
    (R T : Sylow 2 D) (A : Subgroup D) [IsElementaryAbelian 2 A]
    (hAR : A ≤ R) (hAT : A ≤ T)
    (hn : (R : Subgroup D) ≤ normalizer (A : Set D)) (hne : A ≠ ⊥) : R = T := by
  let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 (A.map e.toMonoidHom) := IsElementaryAbelian.map e.toMonoidHom
  have hn' : (R' : Subgroup (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i))) ≤ normalizer (A.map e.toMonoidHom : Set (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i))) :=
    (map_mono hn).trans (le_normalizer_map e.toMonoidHom)
  have hne' : A.map e.toMonoidHom ≠ ⊥ := by
    intro he
    apply hne
    apply (map_injective (f := e.toMonoidHom) e.injective)
    simpa only [Subgroup.map_bot] using he
  have he := original_enlarged_normal_elementary_sylow_unique h i R' T'
    (A.map e.toMonoidHom) (map_mono hAR) (map_mono hAT) hn' hne'
  exact Sylow.ext ((Subgroup.map_injective e.injective) (congrArg Sylow.toSubgroup he))

open Subgroup.CosetGeometry.RankTwo in
/-- Unique Sylow for normal elementary images in every actual local quotient.
No rank-one catalogue premise is required in either vertex orbit. -/
theorem reduced_graph_normal_elementary_sylow_unique (h : HypothesisF11 L S)
    (v : Vertex (reducedFamily L S))
    (R T : Sylow 2 (graphLocalGroup (reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) v)))
    (A : Subgroup (graphLocalGroup (reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) v)))
    [IsElementaryAbelian 2 A] (hAR : A ≤ R) (hAT : A ≤ T)
    (hn : (R : Subgroup (graphLocalGroup (reducedFamily L S) v ⧸ pCore 2 (graphLocalGroup (reducedFamily L S) v))) ≤ normalizer (A : Set (graphLocalGroup (reducedFamily L S) v ⧸ pCore 2 (graphLocalGroup (reducedFamily L S) v)))) (hne : A ≠ ⊥) : R = T := by
  let : ∀ j, Finite ((reducedFamily L S) j) := finite_endpoints (reduced_triple h)
  let : Finite (graphLocalGroup (reducedFamily L S) v) := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let F := reducedFamily L S
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  let M := graphLocalGroup F (Subgroup.CosetGeometry.base F v.type)
  have heq : M.map (MulAut.conj g).toMonoidHom = graphLocalGroup F v :=
    (graphLocalGroup_conjugate (reduced_triple h) g (Subgroup.CosetGeometry.base F v.type)).symm.trans
      (congrArg (graphLocalGroup F) hg)
  let a : M ≃* graphLocalGroup F v :=
    (M.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr heq)
  let e := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
    (reduced_graphEnlargementQuotient h v.type)
  let i : Fin 2 := if v.type then 1 else 0
  have hj : family (enlargedEndpoint L S) v.type = enlargedEndpoint L S i := by
    dsimp only [i]
    cases v.type <;> rfl
  let b := MulEquiv.subgroupCongr hj
  exact marked_enlarged_normal_elementary_sylow_unique h i
    (e.trans (QuotientGroup.congr _ _ b (pCore_map_iso 2 b))) R T A hAR hAT hn hne


open Subgroup.CosetGeometry.RankTwo
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (DGS85.Reduction.G₀ L S))
local notation "G₀" => DGS85.Reduction.G₀ L S

/-- A nontrivial normal elementary edge image fixes only its marked neighbor,
even when the actual quotient is the exceptional enlargement. -/
theorem reduced_normal_elementary_unique_neighbor (h : HypothesisF11 L S)
    {v a c : Vertex F} (hva : (graph F).Adj v a) (hvc : (graph F).Adj v c)
    (A : Subgroup G₀) [IsElementaryAbelian 2 A]
    (hAv : A ≤ stabilizer F v) (hAa : A ≤ stabilizer F a)
    (hAc : A ≤ stabilizer F c) (he : ¬ A ≤ Q F v)
    (hn : (stabilizer F v ⊓ stabilizer F a).pCoreIn 2 ≤ normalizer (A : Set G₀)) : c = a := by
  let ht := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let := finite_endpoints ht
  let M := graphLocalGroup F v
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (reduced_borel_core_sylow h) d hva
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow ht (reduced_borel_core_sylow h) d hvc
  change Sylow 2 M at R T
  change (R : Subgroup M).map M.subtype = _ at hR
  change (T : Subgroup M).map M.subtype = _ at hT
  have hAcore {z : Vertex F} (hvz : (graph F).Adj v z) (hAz : A ≤ stabilizer F z) :
      A ≤ (stabilizer F v ⊓ stabilizer F z).pCoreIn 2 := by
    let E := stabilizer F v ⊓ stabilizer F z
    let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer F v from inf_le_left))
      (inclusion_injective _)
    exact pGroup_le_core_of_core_sylow E A (le_inf hAv hAz)
      (IsElementaryAbelian.isPGroup 2 A) (source_edge_core_sylow ht (reduced_borel_core_sylow h) hvz)
  have hAM : A ≤ M := (hAcore hva hAa).trans (hR ▸ map_subtype_le _)
  let A₀ := A.subgroupOf M
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hAM
  let q := QuotientGroup.mk' (pCore 2 M)
  let E := A₀.map q
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hAR : A₀ ≤ (R : Subgroup M) := by
    intro x hx
    obtain ⟨y,hy,heq⟩ := (hR.symm ▸ hAcore hva hAa hx)
    exact (Subtype.ext heq : y = x) ▸ hy
  have hAT : A₀ ≤ (T : Subgroup M) := by
    intro x hx
    obtain ⟨y,hy,heq⟩ := (hT.symm ▸ hAcore hvc hAc hx)
    exact (Subtype.ext heq : y = x) ▸ hy
  have hnorm : (R : Subgroup M) ≤ normalizer (A₀ : Set M) := by
    intro x hx
    apply le_normalizer_comap M.subtype
    apply hn
    rw [←hR]
    exact mem_map_of_mem M.subtype hx
  have hE : E ≠ ⊥ := by
    intro heq
    have hh := (Subgroup.map_eq_bot_iff _).mp heq
    rw [QuotientGroup.ker_mk'] at hh
    apply he
    intro x hx
    rw [←localGroup_core_eq F d v]
    exact mem_map_of_mem M.subtype (hh (show (⟨x,hAM hx⟩ : M) ∈ A₀ from hx))
  have huniq := reduced_graph_normal_elementary_sylow_unique h
  dsimp only [reducedFamily] at huniq
  let R' : Sylow 2 (M ⧸ pCore 2 M) := R.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let T' : Sylow 2 (M ⧸ pCore 2 M) := T.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hRTq := @huniq v R' T' E (inferInstance : IsElementaryAbelian 2 E)
    (map_mono hAR) (map_mono hAT) ((map_mono hnorm).trans (le_normalizer_map q)) hE
  have hRT : R = T := by
    apply Sylow.ext
    have hh := congrArg (fun U : Sylow 2 (M ⧸ pCore 2 M) => (U : Subgroup _).comap q) hRTq
    change ((R : Subgroup M).map q).comap q = ((T : Subgroup M).map q).comap q at hh
    rw [comap_map_eq,comap_map_eq,show q.ker = pCore 2 M from QuotientGroup.ker_mk' _] at hh
    rwa [sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal R),
      sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T)] at hh
  exact (graph_intrinsic_edgeCore_unique_neighbor ht (reduced_borel_core_sylow h) hva hvc (by
    rw [←hR,hRT,hT]
    exact (pCoreIn_le 2 _).trans inf_le_right)).symm

/-- A critical center has a unique fixed neighbor in the opposite star;
normality in the original edge radical replaces the beta catalogue. -/
theorem reduced_critical_center_unique_neighbor (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) (hfix : Z F a ≤ stabilizer F c) : c = a := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : IsElementaryAbelian 2 (Z F a) := source_center_elementary ht a
  have hab := source_critical_one_adjacent hc hb
  apply reduced_normal_elementary_unique_neighbor h hab.symm hbc (Z F a)
    (((source_Z_Q_U ht a).1.trans (map_subtype_le _)).trans
      ((source_Z_Q_U ht a).2.trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)))
    (Z_le_stabilizer _ a) hfix
    (fun he => hc.2 (he.trans (source_Z_Q_U ht b).2))
  exact ((pCoreIn_le 2 _).trans inf_le_right).trans (stabilizer_normalizes_Z _ a)


private theorem neighbor_critical (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) : IsCriticalPair F c b := by
  let d := reducedFullEarlierLocalTheorems h
  let := finite_endpoints (reduced_triple h)
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨g,hg,hga⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨c,hbc⟩
  have hgb : g • b = b := d.local_le b hg
  change g • a = c at hga
  simpa only [hga,hgb] using criticalPair_translate F hc g

/-- Distinct centers across a critical edge never generate a two-group,
with neither local quotient catalogue assumed. -/
theorem reduced_center_pair_not_isPGroup (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) (hac : a ≠ c) :
    ¬ IsPGroup 2 (Z F a ⊔ Z F c : Subgroup G₀) := by
  let ht := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  have hab := source_critical_one_adjacent hc hb
  have hZa : Z F a ≤ stabilizer F b :=
    (((source_Z_Q_U ht a).1.trans (map_subtype_le _)).trans (source_Z_Q_U ht a).2).trans
      ((ballKernel_one_le_edge _ hab).trans inf_le_right)
  have hZc : Z F c ≤ stabilizer F b :=
    (((source_Z_Q_U ht c).1.trans (map_subtype_le _)).trans (source_Z_Q_U ht c).2).trans
      ((ballKernel_one_le_edge _ hbc.symm).trans inf_le_right)
  intro hp
  obtain ⟨w,hw,hWw⟩ := pGroup_fixes_neighbor ht (reduced_borel_core_sylow h) d hab
    (Z F a ⊔ Z F c) hp (sup_le hZa hZc)
  have hwa := reduced_critical_center_unique_neighbor h hc hb hw (le_sup_left.trans hWw)
  have hwc := reduced_critical_center_unique_neighbor h (neighbor_critical h hc hb hbc) hb hw
    (le_sup_right.trans hWw)
  exact hac (hwa.symm.trans hwc)

/-- The original (11.2)(c) and its nonzero displacement consequence, including
both exceptional local enlargements, follow from F.1.1 alone at distance one. -/
theorem reduced_source_seed_escape (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) (hac : a ≠ c) :
    ¬ Z F a ⊓ Q F b ≤ Q F c ∧ ⁅Z F a ⊓ Q F b,Z F c⁆ ≠ ⊥ := by
  have hn := reduced_center_pair_not_isPGroup h hc hb hbc hac
  exact ⟨source_seed_not_le_opposite_core (reduced_triple h)
      (source_critical_one_adjacent hc hb) hbc hn,
    source_seed_commutator_ne_bot (reduced_triple h)
      (source_critical_one_adjacent hc hb) hbc hn⟩

/-- The two marked neighbors belong to one orbit of their actual center pair,
without an assumed local model or transitivity of that pair on the full star. -/
theorem reduced_source_center_pair_moves (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) :
    ∃ g ∈ Z F a ⊔ Z F c, g • a = c := by
  let ht := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let hB := reduced_borel_core_sylow h
  let hcc := neighbor_critical h hc hb hbc
  let := finite_endpoints ht
  let : IsElementaryAbelian 2 (Z F a) := source_center_elementary ht a
  let : IsElementaryAbelian 2 (Z F c) := source_center_elementary ht c
  have hab := source_critical_one_adjacent hc hb
  have hZa : Z F a ≤ stabilizer F b :=
    (((source_Z_Q_U ht a).1.trans (map_subtype_le _)).trans (source_Z_Q_U ht a).2).trans
      ((ballKernel_one_le_edge _ hab).trans inf_le_right)
  have hZc : Z F c ≤ stabilizer F b :=
    (((source_Z_Q_U ht c).1.trans (map_subtype_le _)).trans (source_Z_Q_U ht c).2).trans
      ((ballKernel_one_le_edge _ hbc.symm).trans inf_le_right)
  let W := Z F a ⊔ Z F c
  have hWb : W ≤ stabilizer F b := sup_le hZa hZc
  let : Finite W := Finite.of_injective (inclusion hWb) (inclusion_injective _)
  obtain ⟨R,hR⟩ := (IsElementaryAbelian.isPGroup 2 (Z F a)).comap_subtype (K := W) |>.exists_le_sylow
  obtain ⟨T,hT⟩ := (IsElementaryAbelian.isPGroup 2 (Z F c)).comap_subtype (K := W) |>.exists_le_sylow
  have hAR : Z F a ≤ (R : Subgroup W).map W.subtype := by
    intro x hx
    exact mem_map_of_mem W.subtype (hR (show (⟨x,mem_sup_left hx⟩ : W) ∈
      (Z F a).subgroupOf W from hx))
  have hCT : Z F c ≤ (T : Subgroup W).map W.subtype := by
    intro x hx
    exact mem_map_of_mem W.subtype (hT (show (⟨x,mem_sup_right hx⟩ : W) ∈
      (Z F c).subgroupOf W from hx))
  have hRa : (R : Subgroup W).map W.subtype ≤ stabilizer F a := by
    obtain ⟨w,hw,hRw⟩ := pGroup_fixes_neighbor ht hB d hab _ (R.isPGroup'.map W.subtype)
      ((map_subtype_le _).trans hWb)
    have he := reduced_critical_center_unique_neighbor h hc hb hw (hAR.trans hRw)
    exact he ▸ hRw
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq W R T
  have hTga : (T : Subgroup W).map W.subtype ≤ stabilizer F ((g : G₀) • a) := by
    rw [←hg]
    change ((R : Subgroup W).map (MulAut.conj g).toMonoidHom).map W.subtype ≤ _
    rw [map_map]
    have he : W.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G₀)).toMonoidHom.comp W.subtype := by ext x; rfl
    rw [he,←map_map,stabilizer_translate]
    exact map_mono hRa
  have hbga : (graph F).Adj b ((g : G₀) • a) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F (g : G₀)).map_adj_iff.mpr hab.symm
    change (graph F).Adj ((g : G₀) • b) ((g : G₀) • a) at hh
    rwa [show (g : G₀) • b = b from hWb g.property] at hh
  exact ⟨g,g.property,reduced_critical_center_unique_neighbor h hcc hb hbga (hCT.trans hTga)⟩

/-- Source (11.3)(a)'s mixed center intersections on the original reduced
graph, with no local quotient catalogue assumed. -/
theorem reduced_source_mixed_center_intersections (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) :
    Z F a ⊓ Q F c = Z F a ⊓ Z F c ∧ Q F a ⊓ Z F c = Z F a ⊓ Z F c := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  have hZa := (source_Z_Q_U ht a).1.trans (map_subtype_le _)
  have hZc := (source_Z_Q_U ht c).1.trans (map_subtype_le _)
  obtain ⟨g,hg,hga⟩ := reduced_source_center_pair_moves h hc hb hbc
  have hcentral : Z F a ⊔ Z F c ≤
      centralizer (Z F a ⊓ Q F c : Set G₀) := by
    apply sup_le
    · exact (le_centralizer_iff.mp (source_core_centralizes_center ht a)).trans
        (centralizer_le (inf_le_left.trans hZa))
    · exact (le_centralizer_iff.mp (source_core_centralizes_center ht c)).trans (centralizer_le inf_le_right)
  have hcentral' : Z F a ⊔ Z F c ≤
      centralizer (Q F a ⊓ Z F c : Set G₀) := by
    apply sup_le
    · exact (le_centralizer_iff.mp (source_core_centralizes_center ht a)).trans (centralizer_le inf_le_left)
    · exact (le_centralizer_iff.mp (source_core_centralizes_center ht c)).trans
        (centralizer_le (inf_le_right.trans hZc))
  constructor
  · apply le_antisymm ?_ (inf_le_inf_left _ hZc)
    intro x hx
    refine ⟨hx.1,?_⟩
    have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom hx.1
    rw [←Z_translate,hga] at hm
    have hh := mem_centralizer_iff.mp (hcentral hg) x hx
    change g*x*g⁻¹ ∈ Z F c at hm
    change x ∈ Z F c
    simpa only [←hh,mul_inv_cancel_right] using hm
  · apply le_antisymm ?_ (inf_le_inf_right _ hZa)
    intro x hx
    refine ⟨?_,hx.2⟩
    have hm := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx.2
    rw [←Z_translate,←hga,inv_smul_smul] at hm
    have hh := mem_centralizer_iff.mp (hcentral' (inv_mem hg)) x hx
    change g⁻¹*x*(g⁻¹)⁻¹ ∈ Z F a at hm
    change x ∈ Z F a
    simpa only [←hh,mul_inv_cancel_right] using hm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
