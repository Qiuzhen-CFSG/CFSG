module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinarySmallInvariant
public import Theory.SpecificGroups.Triality.BinaryTorusElementary
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryCore

/-!
# The elementary image and exact retained kernel in binary local Cartan escape

The original omega-span U is elementary abelian. Transporting that fact through
its literal image in CT/O₂(CT) sharpens the seven-centralizer bound from eight
to four. The same source module recognition identifies U itself, without
changing the original W, as one or two A₅ modules. Thus |U| is 16 or 256,
and the exact kernel E = U intersect O₂(CT) has order at least 4 or 64,
respectively. Neither invariance of E under the component nor a splitting of
the quotient is assumed.

The internal import reuses the quotient-order and normal-extension helpers
from LocalBinaryCore in this continuation of that proof family. The original
Sylow, both Hall conditions, component and quotient maps are retained.
The retained-kernel exclusion and exceptional witness construction remain
open; these bounds do not prove SourceLocalCartanEscape.

Source: Aschbacher--Smith 5.1.10--13, printed pp.634--638, and the
seven-centralizer calculation of 5.2.2, printed pp.648--649,
refs/quasithin.pdf. The root bound is in BinaryTorusElementary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

private theorem seven_fixed_elementary_image_bound
    (S : Sylow 2 G) (R B V : Subgroup G) [IsElementaryAbelian 2 V]
    (hm : Nonempty ((G ⧸ pCore 2 G) ≃*
      Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one))
    [Group.IsPerfect R] (hr : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8)
    (hRN : (S : Subgroup G) ≤ normalizer (R : Set G))
    (hBN : B ≤ normalizer ((R ⊓ (S : Subgroup G) : Subgroup G) : Set G))
    (hB : Nat.card B = 7) (hVS : V ≤ (S : Subgroup G))
    (hfix : V ≤ centralizer (B : Set G)) :
    Nat.card (V.map (QuotientGroup.mk' (pCore 2 G))) ≤ 4 := by
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
  let : IsElementaryAbelian 2 Vbar := IsElementaryAbelian.map q
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map a.toMonoidHom
  let : IsElementaryAbelian 2 (U.subgroupOf Q) := IsElementaryAbelian.subgroupOf hUQ
  have hsize := Triality.Standard.BinaryTorusCentralizer.borel_elementary_subgroup_card_le_four
    (U.subgroupOf Q) (F.subgroupOf Q) hBQ hc
  rwa [Nat.card_congr (subgroupOfEquivOfLe hUQ).toEquiv,
    card_map_of_injective a.injective] at hsize


/-- The literal omega-span image is elementary, sharpening the bound to four. -/
theorem original_binary_triality_elementary_image_bound
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
      Nat.card ((U.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) ≤ 4 := by
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
  let : IsElementaryAbelian 2 U := hu.reduced.2.1
  let : IsElementaryAbelian 2 (U.subgroupOf X) :=
    IsElementaryAbelian.subgroupOf (hu.reduced_le_sylow.trans le_sup_right)
  exact seven_fixed_elementary_image_bound S R (B.subgroupOf X) (U.subgroupOf X)
    hx hrR hRN hBN hBc hVU hfixed


omit [Finite G] in
private theorem oneOrTwo_card {L U : Subgroup G} (hm : IsOneOrTwoA5Modules L U) :
    Nat.card U = 16 ∨ Nat.card U = 256 := by
  have hc : Nat.card (BinaryPermutation.natural (Fin 5)) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)]
    rfl
  rcases hm with ⟨e,f,hf⟩ | ⟨e,f,hf⟩
  · left
    rw [Nat.card_congr f.toEquiv]
    exact hc
  · right
    rw [Nat.card_congr f.toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 5) × BinaryPermutation.natural (Fin 5)) = 256
    rw [Nat.card_prod,hc]

/-- The exact retained kernel has order at least four (at least 64 for
 two copies). The original omega-span itself has one or two A₅ modules. -/
theorem original_binary_triality_elementary_kernel_bound
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
    let E := U ⊓ X.pCoreIn 2
    IsOneOrTwoA5Modules L U ∧
      Nat.card ((U.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) ≤ 4 ∧
      Nat.card U ≤ 4 * Nat.card E ∧
      ((Nat.card U = 16 ∧ 4 ≤ Nat.card E) ∨
        (Nat.card U = 256 ∧ 64 ≤ Nat.card E)) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  obtain ⟨hu,_,_,_,_⟩ := original_binary_triality_fixed_omega_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hn,_,_,hBorel,_,_⟩ := original_binary_triality_module_and_hall
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hHC := (original_container_module_restrictions h hH hgen c hKH hK hKT horbit
    hY hescape C hC hKC hm).2.1
  obtain ⟨F,_,_,hF,⟨f⟩⟩ := h.linear
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card F = 4 by simpa [hn] using hF)
  obtain ⟨hr,hd⟩ := h.whole_deleted_bound_of_borel hH hHC (f.trans a) hBorel
  have hU0 : U ≠ ⊥ := by
    intro he
    apply hu.noncentral
    change ⁅U,L⁆ = ⊥
    rw [he,commutator_bot_left]
  have hmodel := subgroup_oneOrTwoA5_of_whole_deleted h.sylow_normalizes (f.trans a)
    (le_normalizer_conjugateSpanBy _ _) hu.le_wholeReduced hU0 hr hd
  obtain ⟨_,hsize⟩ := original_binary_triality_elementary_image_bound
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨_,_,_,_,_,_,hcount,_,_⟩ := original_binary_triality_core_bound
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hbound : Nat.card U ≤ 4 * Nat.card E := by
    rw [←hcount,Nat.mul_comm 4]
    exact Nat.mul_le_mul_left _ hsize
  refine ⟨hmodel,hsize,hbound,?_⟩
  rcases oneOrTwo_card hmodel with hcard | hcard
  · refine .inl ⟨hcard,?_⟩
    change 4 ≤ Nat.card E
    change Nat.card U = 16 at hcard
    omega
  · refine .inr ⟨hcard,?_⟩
    change 64 ≤ Nat.card E
    change Nat.card U = 256 at hcard
    omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
