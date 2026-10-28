module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryEndpoint
public import Theory.SpecificGroups.Triality.BinaryTorusCentralizer
public import Theory.SpecificGroups.Triality.BinaryGeneratedExtension
public import Theory.GroupTheory.QuotientIntersection
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# The literal core and omega-span image in the binary-triality row

Replace the original local overgroup by X = CT, with C the same containing
component and T the original full Sylow. The original Cartan lies in C,
so the same residual escape persists in X. The quotient X/O₂(X) is
isomorphic to genuine binary triality: its normal simple component has a
two-group quotient and trivial centralizer, and binary triality has no
outer two-automorphisms.

The original residual still has PSL₂(8) two-core quotient. Its image is a
proper perfect subgroup normalized by the full quotient Sylow; the arms
calculation puts that Sylow inside the residual image. The original right
Hall subgroup B normalizes T intersected with the residual, so its image
normalizes this full Sylow. Its order seven survives the two-group kernel.
The original omega-span U is fixed by B. The marked Borel calculation
therefore bounds its image in X/O₂(X) by eight.

The kernel is kept literally as U intersected with O₂(X). The kernel-image
identity gives |U| ≤ 8 |U ∩ O₂(X)|, so this intersection has order at least
two. This is quantitative control of the previously unbounded intersection,
not its vanishing or invariance under L. The binary-triality exclusion and
the full local Cartan witness remain open.

Source: Aschbacher--Smith 5.1.10--13, printed pp.634--638, and the
seven-centralizer argument in 5.2.2, printed pp.648--649,
refs/quasithin.pdf. The quotient correction retains the local two-core.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

private theorem normal_triality_extension (C : Subgroup G) [C.Normal]
    (hC : C.IsCComponent) (S : Sylow 2 G)
    (hgen : C ⊔ (S : Subgroup G) = ⊤)
    (e : (C ⧸ pCore 2 C) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) :
    Nonempty ((G ⧸ pCore 2 G) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let D := C.map q
  let : D.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let a := (cComponentTwoCoreQuotientEquiv hC).symm.trans e
  let : IsSimpleGroup D := a.isSimpleGroup
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
    (f := a.symm.toMonoidHom) a.symm.surjective
  have hsup : D ⊔ (S : Subgroup G).map q = ⊤ := by
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have htwo : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ D) :=
    isPGroup_quotient_of_sup_eq_top D _ (S.isPGroup'.map q) hsup
  have hc := centralizer_eq_bot_of_simple_two_quotient D
    (Group.IsPerfect.not_isMulCommutative D) htwo (pCore_quotient_pCore_eq_bot 2)
  have ht := Triality.Standard.ParabolicOuterTwo.normalExtension_eq_top_at_two D a hc htwo
  exact ⟨((MulEquiv.subgroupCongr ht).trans (topEquiv (G := G ⧸ pCore 2 G))).symm.trans a⟩

private theorem psl_eight_card {Q : Type*} [Group Q]
    (h : ClassicalGroup.IsPSL Q 2 8) : Nat.card Q = 504 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
  rw [hF] at hc
  norm_num [Fin.prod_univ_two] at hc
  rw [Nat.card_congr e.toEquiv]
  omega

private theorem binary_card :
    Nat.card (Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) = 211341312 := by
  rw [Triality.Standard.ConcreteBruhat.FixedCellCount.card_carrier,
    Triality.Standard.ConcreteBruhat.FixedCellCount.card_borel]
  norm_num [Triality.Standard.binaryParameters_q]

private theorem seven_fixed_image_bound
    (S : Sylow 2 G) (R B V : Subgroup G)
    (hm : Nonempty ((G ⧸ pCore 2 G) ≃*
      Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one))
    [Group.IsPerfect R] (hr : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8)
    (hRN : (S : Subgroup G) ≤ normalizer (R : Set G))
    (hBN : B ≤ normalizer ((R ⊓ (S : Subgroup G) : Subgroup G) : Set G))
    (hB : Nat.card B = 7) (hVS : V ≤ (S : Subgroup G))
    (hfix : V ≤ centralizer (B : Set G)) :
    Nat.card (V.map (QuotientGroup.mk' (pCore 2 G))) ≤ 8 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let Rbar := R.map q
  let Bbar := B.map q
  let Vbar := V.map q
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  let r := q.subgroupMap R
  have hk : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let ar := r.pCoreQuotientEquiv (q.subgroupMap_surjective R) hk
  have hrc : Nat.card (Rbar ⧸ pCore 2 Rbar) = 504 :=
    (Nat.card_congr ar.symm.toEquiv).trans (psl_eight_card hr)
  let : Group.IsPerfect Rbar := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective R)
  have hproper : Rbar ≠ ⊤ := by
    intro he
    let a : Rbar ≃* (G ⧸ pCore 2 G) := (MulEquiv.subgroupCongr he).trans (topEquiv (G := G ⧸ pCore 2 G))
    let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    have hcard := Nat.card_congr b.toEquiv
    rw [pCore_quotient_pCore_eq_bot 2,
      Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
      Nat.card_congr hm.some.toEquiv,binary_card,hrc] at hcard
    omega
  have hns : ¬ Group.IsSolvable Rbar := by
    have hnq : Nontrivial (Rbar ⧸ pCore 2 Rbar) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hrc]; decide)
    let : Nontrivial Rbar := Function.Surjective.nontrivial
      (QuotientGroup.mk'_surjective (pCore 2 Rbar))
    exact Group.IsPerfect.not_isSolvable Rbar
  have hPN : (P : Subgroup (G ⧸ pCore 2 G)) ≤ normalizer (Rbar : Set (G ⧸ pCore 2 G)) :=
    (map_mono hRN).trans (le_normalizer_map q)
  obtain ⟨a,ha,hra⟩ := Triality.Standard.BinaryLocalSections.marked_arms
    hm.some P Rbar hproper hns hPN
  have hPR := (Triality.Standard.BinaryLocalSections.sylow_le_and_normalizer_eq
    hm.some P Rbar hproper hns hPN).1
  have hmap : (R ⊓ (S : Subgroup G)).map q = (P : Subgroup _) := by
    rw [map_inf_of_ker_le q R (S : Subgroup G) (by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S)]
    exact inf_eq_right.mpr hPR
  have hBP : Bbar ≤ normalizer (P : Set _) := by
    change Bbar ≤ normalizer ((P : Subgroup (G ⧸ pCore 2 G)) : Set (G ⧸ pCore 2 G))
    rw [←hmap]
    exact (map_mono hBN).trans (le_normalizer_map q)
  let F := Bbar.map a.toMonoidHom
  let U := Vbar.map a.toMonoidHom
  let Q := Triality.Standard.Parabolics.borel (Triality.Standard.binaryParameters 1 Nat.zero_lt_one)
  have hFQ : F ≤ Q := by
    have hh := (map_mono hBP).trans (le_normalizer_map a.toMonoidHom)
    rw [ha,Triality.Standard.ConcreteBruhat.normalizer_unipotent_eq_borel _ rfl] at hh
    exact hh
  have hUQ : U ≤ Q :=
    ((map_mono (map_mono hVS)).trans_eq ha).trans
      (Triality.Standard.Parabolics.unipotent_le_borel _)
  have hUF : U ≤ centralizer (F : Set _) :=
    (map_mono ((map_mono hfix).trans (map_centralizer_le_centralizer_image B q))).trans
      (map_centralizer_le_centralizer_image Bbar a.toMonoidHom)
  have hcardB : Nat.card Bbar = 7 := by
    have hdis : Disjoint B q.ker := by
      apply disjoint_of_coprime_natCard
      obtain ⟨k,hk⟩ := (show IsPGroup 2 q.ker by
        rw [QuotientGroup.ker_mk']; exact pCore_isPGroup).exists_card_eq
      rw [hB,hk]
      exact (by decide : Nat.Coprime 7 2).pow_right k
    have hi : Function.Injective (q.subgroupMap B) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro x hx
      apply Subtype.ext
      exact disjoint_def.mp hdis x.property
        (show (x : G) ∈ q.ker from congrArg Subtype.val hx)
    rw [←Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap B)
      ⟨hi,q.subgroupMap_surjective B⟩).toEquiv,hB]
  have hBQ : Nat.card (F.subgroupOf Q) = 7 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hFQ).toEquiv,
      card_map_of_injective a.injective]
    exact hcardB
  have hc : U.subgroupOf Q ≤ centralizer (F.subgroupOf Q : Set Q) := by
    intro u hu f hf
    exact Subtype.ext (hUF hu f hf)
  have hsize := Triality.Standard.BinaryTorusCentralizer.borel_two_subgroup_card_le_eight
    (U.subgroupOf Q) (F.subgroupOf Q)
    (((S.isPGroup'.to_le hVS).map q).map a.toMonoidHom |>.comap_subtype)
    hBQ hc
  rwa [Nat.card_congr (subgroupOfEquivOfLe hUQ).toEquiv,
    card_map_of_injective a.injective] at hsize

/-- The exact two-core quotient of the component--Sylow join and the
image-size bound for the original seven-fixed omega-span. -/
theorem original_binary_triality_omega_image_bound
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    Nonempty ((X ⧸ pCore 2 X) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) ∧
      Nat.card ((U.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) ≤ 8 := by
  obtain ⟨hKR,hCn,hr⟩ := LocalSieve.binaryTriality_residual_section h.qtke hKH
    hH.1.1.2 hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hu,_,hb,hfix,_⟩ := original_binary_triality_fixed_omega_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  have hXY : X ≤ Y := sup_le (map_subtype_le C) (hH.1.1.2.trans hY.2)
  let D := (C.map Y.subtype).subgroupOf X
  have hCY : ((C.map Y.subtype).subgroupOf Y).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hC
  have hD : D.IsCComponent := hCY.subgroupOf_of_le le_sup_left hXY
  have hCNY : ((C.map Y.subtype).subgroupOf Y).Normal := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hCn
  have hCN : Y ≤ normalizer (C.map Y.subtype : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp hCNY
  let : D.Normal := normal_subgroupOf_of_le_normalizer (hXY.trans hCN)
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let a := (C.equivMapOfInjective Y.subtype Y.subtype_injective).trans
    (subgroupOfEquivOfLe (show C.map Y.subtype ≤ X from le_sup_left)).symm
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  obtain ⟨em⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ 1 Nat.zero_lt_one).mp
    (show Triality.Standard.IsTrialityGroupAt (2^1) (C ⧸ pCore 2 C) by simpa using hm)
  have hDS : D ⊔ (S : Subgroup X) = ⊤ := by
    apply map_injective X.subtype_injective
    change ((C.map Y.subtype).subgroupOf X ⊔ (T : Subgroup G).subgroupOf X).map
      X.subtype = (⊤ : Subgroup X).map X.subtype
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right,←MonoidHom.range_eq_map,range_subtype]
  have hx := normal_triality_extension D hD S hDS (aq.symm.trans em)
  refine ⟨hx,?_⟩
  have hRX : residual H ≤ X := (hKR ▸ hKC).trans le_sup_left
  let R := (residual H).subgroupOf X
  let ar := ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (subgroupOfEquivOfLe hRX).symm
  let arq := QuotientGroup.congr _ _ ar (pCore_map_iso 2 ar)
  have hrR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 := hr.of_mulEquiv arq.symm
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK
  let : Group.IsPerfect (residual H) := hKR ▸ (inferInstance : Group.IsPerfect K)
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRX).symm.toMonoidHom) (subgroupOfEquivOfLe hRX).symm.surjective
  have hRN : (S : Subgroup X) ≤ normalizer (R : Set X) := by
    rw [←subgroupOf_normalizer_eq hRX]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_residual H))
  have hBNG : B ≤ normalizer ((residual H ⊓ (T : Subgroup G) : Subgroup G) : Set G) := by
    rw [inf_comm]
    exact (le_inf (c.right_le.trans inf_le_left) (Global.right_cartan_le_residual c)).trans
      (Global.rankOne_residual_geometry h.sylow_normalizes hH (.linear 3 (by decide)
        (by simpa using hr))).two_closed
  have hBN : B.subgroupOf X ≤ normalizer ((R ⊓ (S : Subgroup X) : Subgroup X) : Set X) := by
    intro b hb
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hBNG hb) (x : G)
  have hBX : B ≤ X := (Global.right_cartan_le_residual c).trans hRX
  have hBc : Nat.card (B.subgroupOf X) = 7 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBX).toEquiv]
    exact hb
  have hVU : U.subgroupOf X ≤ (S : Subgroup X) := comap_mono hu.reduced_le_sylow
  have hfixed : U.subgroupOf X ≤ centralizer (B.subgroupOf X : Set X) := by
    intro u hu b hb
    exact Subtype.ext ((le_centralizer_iff.mp hfix) hu b hb)
  exact seven_fixed_image_bound S R (B.subgroupOf X) (U.subgroupOf X)
    hx hrR hRN hBN hBc hVU hfixed

/-- The original escape persists in the component--Sylow join. Its
omega-span image has at most eight elements, with the exact lost kernel
retained in the cardinal identity and bound. -/
theorem original_binary_triality_core_bound
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let q := QuotientGroup.mk' (pCore 2 X)
    X ≤ Y ∧ X ∈ Chapter1.HOver G (H : Set G) ∧ A ≤ X ∧
      ¬ A ⊓ X ≤ normalizer (residual H : Set G) ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) ∧
      Nat.card ((U.subgroupOf X).map q) ≤ 8 ∧
      Nat.card (U ⊓ X.pCoreIn 2 : Subgroup G) *
        Nat.card ((U.subgroupOf X).map q) = Nat.card U ∧
      Nat.card U ≤ 8 * Nat.card (U ⊓ X.pCoreIn 2 : Subgroup G) ∧
      2 ≤ Nat.card (U ⊓ X.pCoreIn 2 : Subgroup G) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let q := QuotientGroup.mk' (pCore 2 X)
  obtain ⟨hx,hsize⟩ := original_binary_triality_omega_image_bound
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hu,hlower,_,_,_⟩ := original_binary_triality_fixed_omega_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hAX : A ≤ X := (original_binary_triality_module_and_hall
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm).2.2.1.trans le_sup_left
  have hXY : X ≤ Y := sup_le (map_subtype_le C) (hH.1.1.2.trans hY.2)
  have hHX : H ≤ X := by rw [←hKT]; exact sup_le (hKC.trans le_sup_left) le_sup_right
  have hXH : X ∈ Chapter1.HOver G (H : Set G) := by
    refine ⟨?_,hHX⟩
    intro hz
    exact hY.1 (bot_unique ((pCoreIn_le_pCoreIn_of_sylow T le_sup_right hXY).trans_eq hz))
  have hesc : ¬ A ⊓ X ≤ normalizer (residual H : Set G) := by
    rw [inf_eq_left.mpr hAX]
    exact fun hh => hescape (inf_le_left.trans hh)
  have hUX : U ≤ X := hu.reduced_le_sylow.trans le_sup_right
  have he : ((U.subgroupOf X) ⊓ pCore 2 X).map X.subtype =
      U ⊓ X.pCoreIn 2 := by
    rw [map_inf _ _ X.subtype X.subtype_injective,map_subgroupOf_eq_of_le hUX]
    rfl
  have hkcard : Nat.card ((U.subgroupOf X) ⊓ pCore 2 X : Subgroup X) =
      Nat.card (U ⊓ X.pCoreIn 2 : Subgroup G) := by
    rw [←card_map_of_injective (K := (U.subgroupOf X) ⊓ pCore 2 X) X.subtype_injective,he]
  have hcount := IsElementaryAbelian.card_inf_ker_mul_card_map (U.subgroupOf X) q
  rw [QuotientGroup.ker_mk',hkcard,Nat.card_congr (subgroupOfEquivOfLe hUX).toEquiv] at hcount
  have hbound : Nat.card U ≤ 8 * Nat.card (U ⊓ X.pCoreIn 2 : Subgroup G) := by
    rw [←hcount,Nat.mul_comm 8]
    exact Nat.mul_le_mul_left _ hsize
  refine ⟨hXY,hXH,hAX,hesc,hx,hsize,hcount,hbound,?_⟩
  change 16 ≤ Nat.card U at hlower
  change 2 ≤ Nat.card (U ⊓ X.pCoreIn 2 : Subgroup G)
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
