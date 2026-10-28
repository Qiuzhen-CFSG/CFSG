module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryProduct
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometrySetup
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Endpoints
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import Theory.GroupTheory.ReducedNormal.Equiv
public import Theory.GroupTheory.PResidual.NormalClosureCover
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The actual escaping coset graph and its even critical pairs

Uniqueness over LT constructs the core-free F.7 setup for LT and an
outside overgroup H of T. In the escaping centralizer branch, finite
minimal descent selects H in H-star inside IT. Its two-residual lies in I,
its generation parameter is one, and its two-core contains the natural
seed. The H-closure of that seed lies in the literal escaping closure U.

An even critical pair gives two noncommuting mutually normalizing natural
layers. Sylow conjugacy inside the seed normalizer and source 6.1.11 fuse
them into I, proving that U is nonabelian. Consequently an abelian U
produces the actual odd critical configuration at distance at least three,
with an elementary H-closure and a normalized endpoint. The odd-distance
argument of 6.1.19 remains with qt-d-1222-rankone-recognition-natural,
along with the initial action and final 6.1.27 assembly.

Source: Aschbacher–Smith, 6.1.16–20, printed pp.672–675; F.7.6 and
F.7.11, printed pp.312–314. The graph construction uses the same finite
subgroup transports as the independent local-graph setup for 6.2.8, without
using that later theorem or its 6.1.27 hypothesis.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.ChapterF.Section07.Track
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph
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
private theorem setup_of_unique (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
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


/-- Uniqueness over LT follows from the actual local-family hypothesis. -/
private theorem unique_overgroup (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n) :
    ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M := by
  have hstar : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h.local_mem.1.prop, ?_⟩
    intro J hJ hLJ
    exact le_antisymm (h.local_mem.1.2 hJ hLJ) hLJ
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.simpleQTKE T hstar
  have horbit : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl h.sylow_normalizes_L)
      (le_componentOrbit L T)
  intro N hN hLN
  have h1 := hu.normalizer_unique N hN
  have h2 := hu.normalizer_unique M h.maximal
  rw [horbit] at h1 h2
  exact (h1 hLN).trans (h2 (sup_le h.L_le h.sylow_le)).symm

/-- The actual F.7 setup needs no separate uniqueness assumption. -/
theorem setup (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H) (hHM : ¬ H ≤ M) :
    let X := L ⊔ (T : Subgroup G)
    let K := X ⊔ H
    let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K else X.subgroupOf K
    ∃ D : SourceSetup F, D.V ≠ ⊥ ∧
      D.seed.map K.subtype = layer L R ∧
      (D.sylow false : Subgroup (F false)).map
        (K.subtype.comp (F false).subtype) = (T : Subgroup G) :=
  setup_of_unique h hnat (unique_overgroup h) hTH hHM

private theorem residual_le_centralizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    {H : Subgroup G} (hHJ : H ≤ Escape.I (T : Subgroup G) L R ⊔ (T : Subgroup G)) :
    (pResidual 2 H).map H.subtype ≤ Escape.I (T : Subgroup G) L R := by
  let I := Escape.I (T : Subgroup G) L R
  let J := I ⊔ (T : Subgroup G)
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) :=
    h.sylow_normalizes_ZS.trans (normalizer_le_normalizer_centralizer _)
  let : (I.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer (sup_le I.le_normalizer hTI)
  have hj : I.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show I ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hp : IsPGroup 2 (J ⧸ I.subgroupOf J) := isPGroup_quotient_of_sup_eq_top
    (I.subgroupOf J) ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype hj
  let f := (QuotientGroup.mk' (I.subgroupOf J)).comp (inclusion hHJ)
  have hk : pResidual 2 H ≤ f.ker := pResidual_le_ker_of_isPGroup 2 f hp
  rintro _ ⟨x,hx,rfl⟩
  exact (QuotientGroup.eq_one_iff (N := I.subgroupOf J) (inclusion hHJ x)).mp
    (MonoidHom.mem_ker.mp (hk hx))

/-- Source 6.1.16 supplies an actual minimal outside vertex with residual
in I. Its core contains the natural seed, and its local closure lies in U. -/
theorem exists_vertex (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hI : ¬ Escape.I (T : Subgroup G) L R ≤ M) :
    ∃ H ∈ Chapter3.HStar (T : Subgroup G) M,
      H ≤ Escape.I (T : Subgroup G) L R ⊔ (T : Subgroup G) ∧
      (pResidual 2 H).map H.subtype ≤ Escape.I (T : Subgroup G) L R ∧
      ChapterE.generationParameter H = 1 ∧
      H ⊓ normalizer (layer L R : Set G) = H ⊓ M ∧
      H ⊓ M ⋖ H ∧
      (∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ⋖ H → X = H ⊓ M) ∧
      layer L R ≤ H.pCoreIn 2 ∧
      conjugateSpanBy (layer L R) H ≤ Escape.U (T : Subgroup G) L R := by
  classical
  let I := Escape.I (T : Subgroup G) L R
  let J := I ⊔ (T : Subgroup G)
  let N := Escape.H (T : Subgroup G) L R
  have hJN : J ≤ N := sup_le (Subgroup.centralizer_le_normalizer _) h.sylow_normalizes_ZS
  have hN : N ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal ⟨ZS (T : Subgroup G) L R, h.ZS_ne_bot,
      T.isPGroup'.to_le h.ZS_le_T, rfl⟩, h.sylow_normalizes_ZS⟩
  have hJ : J ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T le_sup_right hJN hN
  let S : Set (Subgroup G) := {H | H ∈ Chapter1.HOver G (T : Set G) ∧ ¬ H ≤ M ∧ H ≤ J}
  have hS : S.Nonempty := ⟨J,hJ,fun hJM => hI (le_sup_left.trans hJM),le_rfl⟩
  obtain ⟨H,hH⟩ := (Set.toFinite S).exists_minimalFor id S hS
  have hstar : H ∈ Chapter3.HStar (T : Subgroup G) M := by
    refine ⟨⟨hH.1.1,hH.1.2.1⟩,?_⟩
    intro X hX hXH
    exact hH.2 ⟨hX.1,hX.2,hXH.trans hH.1.2.2⟩ hXH
  have hHN : H ≤ N := hH.1.2.2.trans hJN
  have hnorm : H ⊓ normalizer (layer L R : Set G) = H ⊓ M := by
    apply le_antisymm (inf_le_inf_left _ hE.normalizer_le)
    intro x hx
    exact ⟨hx.1,inf_normalizer_le_of_trivial_intersections hE.ti h.ZS_ne_bot
      inf_le_left ⟨hx.2,hHN hx.1⟩⟩
  have hcore : layer L R ≤ H.pCoreIn 2 :=
    ((Escape.layer_le_U _ _ _).trans
      (natural_escape_frattini_and_normalizer_core h hnat hE hNS).2.1).trans
        (Chapter3.twoCore_le_of_sylow_le T hstar.1.1.2 hHN)
  refine ⟨H,hstar,hH.1.2.2,residual_le_centralizer h hH.1.2.2,
    h.generation_one H hstar,hnorm,
    (Chapter3.HStar.unique_maximal T h.sylow_le hstar).2.1,
    (Chapter3.HStar.unique_maximal T h.sylow_le hstar).2.2,hcore,?_⟩
  rw [←natural_escape_normalizer_span h hE hNS]
  exact conjugateSpanBy_mono le_rfl hHN

/-- A noncommuting mutually normalizing conjugate pair already proves
nonabelianness of the literal I-closure, even before aligning with T. -/
theorem nonabelian_of_pair
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (g : G) (hne : ⁅layer L R,(layer L R).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅layer L R,(layer L R).map (MulAut.conj g).toMonoidHom⁆ ≤
      layer L R ⊓ (layer L R).map (MulAut.conj g).toMonoidHom) :
    ¬ Escape.U (T : Subgroup G) L R ≤ centralizer (Escape.U (T : Subgroup G) L R : Set G) := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let N := normalizer (B : Set G)
  have hAN : A ≤ N := le_normalizer_iff_commutator_le_left.mpr (hcomm.trans inf_le_left)
  let := h.layer_elementary
  have hp : IsPGroup 2 (A.subgroupOf N) :=
    ((IsElementaryAbelian.isPGroup 2 B).map (MulAut.conj g).toMonoidHom).comap_subtype
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  obtain ⟨m,hm⟩ := MulAction.exists_smul_eq N P (T.subtype h.sylow_normalizes_layer)
  have hmap : (P : Subgroup N).map (MulAut.conj m).toMonoidHom = (T : Subgroup G).subgroupOf N := by
    change ((m • P : Sylow 2 N) : Subgroup N) = _
    rw [hm,Sylow.coe_subtype]
  have hAT : A.map (MulAut.conj (m : G)).toMonoidHom ≤ (T : Subgroup G) := by
    rintro _ ⟨a,ha,rfl⟩
    have hh : (MulAut.conj m) (⟨a,hAN ha⟩ : N) ∈ (T : Subgroup G).subgroupOf N :=
      hmap ▸ mem_map_of_mem (MulAut.conj m).toMonoidHom
        (hP (show (⟨a,hAN ha⟩ : N) ∈ A.subgroupOf N from ha))
    exact hh
  have hB : B.map (MulAut.conj (m : G)).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp m.property
  have hA : A.map (MulAut.conj (m : G)).toMonoidHom =
      B.map (MulAut.conj ((m : G) * g)).toMonoidHom := by
    rw [show A = B.map (MulAut.conj g).toMonoidHom from rfl,map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  have hne' : ⁅B,B.map (MulAut.conj ((m : G) * g)).toMonoidHom⁆ ≠ ⊥ := by
    intro hz
    apply hne
    apply (map_eq_bot_iff_of_injective _ (f := (MulAut.conj (m : G)).toMonoidHom)
      (MulAut.conj (m : G)).injective).mp
    rwa [map_commutator,hB,hA]
  have hcomm' := map_mono (f := (MulAut.conj (m : G)).toMonoidHom) hcomm
  change ⁅B,A⁆.map (MulAut.conj (m : G)).toMonoidHom ≤
    (B ⊓ A).map (MulAut.conj (m : G)).toMonoidHom at hcomm'
  rw [map_commutator,map_inf _ _ _ (MulAut.conj (m : G)).injective,hB,hA] at hcomm'
  rw [hA] at hAT
  obtain ⟨_,_,_,_,c,hc,he⟩ := mutual_conjugate_source_of_natural h hnat hE hs
    (central_line_factorization_of_S_normalizer h hNS) ((m : G) * g) hAT hne' hcomm'
  have hBU : B ≤ Escape.U (T : Subgroup G) L R := Escape.layer_le_U _ _ _
  have hAU : B.map (MulAut.conj ((m : G) * g)).toMonoidHom ≤ Escape.U (T : Subgroup G) L R := by
    rw [he]
    exact le_iSup (fun i : Escape.I (T : Subgroup G) L R =>
      B.map (MulAut.conj (i : G)).toMonoidHom) ⟨c,hc⟩
  intro hab
  exact hne' (commutator_eq_bot_iff_le_centralizer.mpr
    (hBU.trans (hab.trans (centralizer_le hAU))))

open Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Section07.CriticalPairs

/-- The even critical-distance branch of 6.1.20(2), on the actual coset graph. -/
theorem nonabelian_of_even_track
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    {H : Subgroup G}
    (D : SourceSetup (fun i => if i then H.subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H)
      else (L ⊔ (T : Subgroup G)).subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H)))
    (hne : D.V ≠ ⊥)
    (hseed : D.seed.map ((L ⊔ (T : Subgroup G)) ⊔ H).subtype = layer L R)
    (heven : Even (D.track hne)) :
    ¬ Escape.U (T : Subgroup G) L R ≤ centralizer (Escape.U (T : Subgroup G) L R : Set G) := by
  let K := (L ⊔ (T : Subgroup G)) ⊔ H
  let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
    else (L ⊔ (T : Subgroup G)).subgroupOf K
  obtain ⟨v,hd,hcrit⟩ := (D.critical_witness hne).1
  have hv := even_endpoint_type F D hne hd heven
  have hp := SourceAction.even_critical_pair D hne hd heven hcrit
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  rw [vertexModule_first F D.seed hv,←hg,
    firstModule_translate_base F D.seed D.seed_normalized] at hp
  have hconj : (D.seed.map (MulAut.conj g).toMonoidHom).map K.subtype =
      (layer L R).map (MulAut.conj (g : G)).toMonoidHom := by
    rw [map_map]
    have he : K.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp K.subtype := rfl
    rw [he,←map_map,hseed]
  have hbound := map_mono (f := K.subtype) hp.2.1
  rw [map_commutator,map_inf _ _ _ K.subtype_injective,hseed,hconj] at hbound
  apply nonabelian_of_pair h hnat hE hs hNS (g : G) ?_ hbound
  intro hz
  apply hp.1
  apply (map_eq_bot_iff_of_injective _ K.subtype_injective).mp
  rwa [map_commutator,hseed,hconj]

/-- All literal data at the start of the odd-distance argument in 6.1.19.
The endpoint is a vertex of the actual LT,H graph; no conclusion of
6.1.19 or of the natural reduction is a field of this structure. -/
structure OddConfiguration (T : Sylow 2 G) (L M R : Subgroup G) where
  H : Subgroup G
  hstar : H ∈ Chapter3.HStar (T : Subgroup G) M
  overgroup : H ≤ Escape.I (T : Subgroup G) L R ⊔ (T : Subgroup G)
  residual : (pResidual 2 H).map H.subtype ≤ Escape.I (T : Subgroup G) L R
  generation : ChapterE.generationParameter H = 1
  normalizer : H ⊓ Subgroup.normalizer (layer L R : Set G) = H ⊓ M
  maximal : H ⊓ M ⋖ H
  unique_maximal : ∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ⋖ H → X = H ⊓ M
  core : layer L R ≤ H.pCoreIn 2
  closure_le : conjugateSpanBy (layer L R) H ≤ Escape.U (T : Subgroup G) L R
  closure_elementary : IsElementaryAbelian 2 (conjugateSpanBy (layer L R) H)
  D : SourceSetup (fun i => if i then H.subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H)
    else (L ⊔ (T : Subgroup G)).subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H))
  seed_ne : D.V ≠ ⊥
  seed_map : D.seed.map ((L ⊔ (T : Subgroup G)) ⊔ H).subtype = layer L R
  odd : Odd (D.track seed_ne)
  distance : 3 ≤ D.track seed_ne
  endpoint : NormalizedEndpoint D seed_ne
  pair : let K := (L ⊔ (T : Subgroup G)) ⊔ H
    let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
      else (L ⊔ (T : Subgroup G)).subgroupOf K
    ⁅vertexModule F D.seed (base F true),vertexModule F D.seed endpoint.vertex⁆ ≤
      vertexModule F D.seed (base F true) ⊓ vertexModule F D.seed endpoint.vertex

/-- If the escaping closure were abelian, the source produces an odd
critical distance at least three and the elementary local closure in 6.1.19. -/
theorem odd_configuration_of_abelian
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hI : ¬ Escape.I (T : Subgroup G) L R ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤ centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    Nonempty (OddConfiguration T L M R) := by
  obtain ⟨H,hH,hHJ,hres,hgen,hnorm,hmax,huniq,hcore,hclosure⟩ :=
    exists_vertex h hnat hE hNS hI
  obtain ⟨D,hne,hseed,_⟩ := setup h hnat hH.1.1.2 hH.1.2
  let K := (L ⊔ (T : Subgroup G)) ⊔ H
  let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
    else (L ⊔ (T : Subgroup G)).subgroupOf K
  have hodd : Odd (D.track hne) := (Nat.even_or_odd _).resolve_left
    (fun he => nonabelian_of_even_track h hnat hE hs hNS D hne hseed he hab)
  have htrue : (F true).map K.subtype = H := map_subgroupOf_eq_of_le le_sup_right
  have hcore' : D.seed ≤ (F true).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective K.subtype_injective).mp
    rw [map_pCoreIn_of_injective 2 _ _ K.subtype_injective,htrue,hseed]
    exact hcore
  have hb1 := Completion.one_lt_track_of_true_core F D hne hcore'
  have hb : 3 ≤ D.track hne := by
    obtain ⟨k,hk⟩ := hodd
    omega
  have hel : IsElementaryAbelian 2 (conjugateSpanBy D.seed (F true)) := by
    rw [conjugateSpanBy_eq_iSup_conj]
    exact Completion.conjugate_join_elementary_of_odd F D hne hcore' hodd
  have hel' : IsElementaryAbelian 2 (conjugateSpanBy (layer L R) H) := by
    let := hel
    have hh := IsElementaryAbelian.map K.subtype (p := 2) (A := conjugateSpanBy D.seed (F true))
    rwa [map_conjugateSpanBy,hseed,htrue] at hh
  obtain ⟨e⟩ := NormalizedEndpoint.nonempty (D := D) (hne := hne) hodd
  exact ⟨{
    H := H
    hstar := hH
    overgroup := hHJ
    residual := hres
    generation := hgen
    normalizer := hnorm
    maximal := hmax
    unique_maximal := huniq
    core := hcore
    closure_le := hclosure
    closure_elementary := hel'
    D := D
    seed_ne := hne
    seed_map := hseed
    odd := hodd
    distance := hb
    endpoint := e
    pair := e.commutator_le hb }⟩

/-- Source 6.1.20(2) is reduced to its odd-distance branch, with every
coset-graph, minimal-vertex and even-branch premise constructed. -/
theorem nonabelian_or_odd_configuration
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hI : ¬ Escape.I (T : Subgroup G) L R ≤ M) :
    (¬ Escape.U (T : Subgroup G) L R ≤ centralizer (Escape.U (T : Subgroup G) L R : Set G)) ∨
      Nonempty (OddConfiguration T L M R) := by
  classical
  by_cases hab : Escape.U (T : Subgroup G) L R ≤ centralizer (Escape.U (T : Subgroup G) L R : Set G)
  · exact Or.inr (odd_configuration_of_abelian h hnat hE hs hNS hI hab)
  · exact Or.inl hab

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph
