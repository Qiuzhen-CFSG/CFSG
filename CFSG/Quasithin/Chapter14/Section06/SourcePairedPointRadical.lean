module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPointThompson
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointCentralizer
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicGeneration
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.RadicalNormalizerControl

/-!
# The literal paired point-centralizer radical in 14.6.9

For the paired alternating-five branch, the marked block actions identify
J(O₂(I∩M_c)) with O₂(I). The original I-star normalizer control makes the
same R Sylow in N_{M_c}(O₂(I∩M_c)), so the latter core is radical in M_c.
The radical normalizer lemma gives Q₁≤O₂(I∩M_c); suitability then gives
R=T₀. Characteristic two supplies the required central-involution inclusion.
All subgroups and normalizers are the literal source subgroups.

Source: Aschbacher--Smith, proof of 14.6.9, printed pp.1025--1026
(refs/quasithin.pdf).
-/

public section
open Subgroup BinaryPermutation
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory Stellmacher
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual point-centralizer core has Thompson subgroup O₂(I). -/
theorem source_paired_point_thompson
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hpairIndex : (((T : Subgroup G) ⊓ I).relIndex Λ) = 2) :
    elementaryAbelianMaxJ ((I ⊓ Mc).pCoreIn 2) = I.pCoreIn 2 := by
  let R := (T : Subgroup G) ⊓ I
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  let K := (pResidual 2 I).map I.subtype
  let S := ChapterB.baumann R
  let B := I ⊓ Mc
  let W := B.pCoreIn 2
  obtain ⟨z,hz,heq,hzS,hzR,hout,h,v,hv,hcentral,hpoint⟩ :=
    source_paired_block_point_marking hG T hempty hM hunique hmany hcard e hab
      H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨_,⟨h'⟩⟩ := c.alternating_paired_setups b i j hij hs hi
  obtain ⟨_,_,_,_,_,hout',_⟩ := source_paired_block_point_marking
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b j i hij.symm hs h'.block
  have hRB : R ≤ B := le_inf inf_le_right (by
    intro r hr
    rw [←heq]
    exact mem_centralizer_singleton_iff.mpr (hzR r hr))
  have hWn : B ≤ normalizer (W : Set G) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hW2 : IsPGroup 2 W := isPGroup_pCoreIn 2 B
  have hWc : W ≤ centralizer ({z} : Set G) := (pCoreIn_le 2 B).trans
    (inf_le_right.trans heq.ge)
  have hNi : K₁ ⊔ S ≤ I := sup_le (map_subtype_le _) (inf_le_left.trans inf_le_right)
  have hNj : K₂ ⊔ S ≤ I := sup_le (map_subtype_le _) (inf_le_left.trans inf_le_right)
  have hWnorm (N : Subgroup G) (hNI : N ≤ I) :
      N ⊓ centralizer ({z} : Set G) ≤ normalizer (W : Set G) := by
    intro a ha
    exact hWn ⟨hNI ha.1,heq ▸ ha.2⟩
  have heven := h.central_point_twoGroup_image_even z hzS hzR (heq.symm ▸ hout)
    W hW2 hWc (hWnorm _ hNi)
  have heven' := h'.central_point_twoGroup_image_even z hzS hzR (heq.symm ▸ hout')
    W hW2 hWc (hWnorm _ hNj)
  have hQI : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hQR : I.pCoreIn 2 ≤ R := (pCoreIn_le_sylow I c.sylow).trans_eq c.sylow_image
  have hQW : I.pCoreIn 2 ≤ W := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 I) (hQR.trans hRB) (inf_le_left.trans hQI)
  obtain ⟨PB,hPB⟩ := c.sylow.exists_map_subtype_eq_of_le
    (show B ≤ I from inf_le_left) (by rw [c.sylow_image]; exact hRB)
  have hWR : W ≤ R := (pCoreIn_le_sylow B PB).trans_eq (hPB.trans c.sylow_image)
  have hjoin : K₁ ⊔ K₂ = K := c.pair_join b i j hij hs
  have hRK : R ≤ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    rw [hjoin]
    exact c.R_le_H.trans c.normalizes_residual
  have hIgen : I = (K₁ ⊔ K₂) ⊔ R := by rw [hjoin,c.residual_sup_sylow]
  have hno (A : Subgroup G) (hAR : A ≤ R) (hIA : I ≤ normalizer (A : Set G))
      (hΛA : Λ ≤ normalizer (A : Set G)) : A = ⊥ :=
    c.no_common_normal A hAR ((normal_subgroupOf_iff_le_normalizer
      (hAR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hΛA hIA))
  have hpair : ∀ r ∈ R, K₁.conjBy r = K₁ ∨ K₁.conjBy r = K₂ :=
    c.pair_action b i j hij hs
  obtain ⟨t,ht,_,hte⟩ := c.pair_exchange b i j hij
  have ht' : ∃ t : Λ, (t : G) ∈ R ∧ K₁.conjBy (t : G) = K₂ :=
    ⟨⟨t,c.R_le_M ht⟩,ht,hte⟩
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule K₁).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K₁ : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  have hfull : R ⊓ centralizer ((sourceModule K₁ ⊔ sourceModule K₂ : Subgroup G) : Set G) =
      I.pCoreIn 2 := by
    simpa only [ambientModule_eq_literal,K₁,K₂,R,ChapterC.Section05.ConjugateSource.sourceModule,moduleLayer] using
      Section06.Original.pair_core_centralizer c b i j hij hs
  have hfullS : S ⊓ centralizer ((sourceModule K₁ ⊔ sourceModule K₂ : Subgroup G) : Set G) =
      I.pCoreIn 2 := (h.two_block_full_centralizer_eq h' I Λ R c.R_le_M c.T_le
        c.R_normal hRK hIgen hno x hx hpairIndex hpair ht' hnc).1.symm.trans hfull
  exact (h.two_block_even_thompson h' I Λ R c.T_le c.R_normal hRK hIgen hno
    x hx hpairIndex hpair ht' hnc W (hfullS ▸ hQW) hWR heven heven').trans hfullS

end CFSG.Quasithin.Chapter14.Section06

namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory Stellmacher
variable {G : Type*} [Group G] [Finite G]

private theorem ambient_core_le_radical
    (M W : Subgroup G) (hWM : W ≤ M) (hW : IsPGroup 2 W)
    (hrad : (M ⊓ normalizer (W : Set G)).pCoreIn 2 ≤ W) : M.pCoreIn 2 ≤ W := by
  let W₀ := W.subgroupOf M
  have hmapN : (normalizer (W₀ : Set M)).map M.subtype = M ⊓ normalizer (W : Set G) := by
    rw [←subgroupOf_normalizer_eq hWM,subgroupOf_map_subtype,inf_comm]
  have hrad₀ : (normalizer (W₀ : Set M)).pCoreIn 2 ≤ W₀ := by
    intro w hw
    have hm := mem_map_of_mem M.subtype hw
    rw [map_pCoreIn_of_injective 2 _ M.subtype M.subtype_injective,hmapN] at hm
    exact hrad hm
  have hh := pCore_le_of_pCore_normalizer_le W₀ hW.comap_subtype hrad₀
  rintro q ⟨a,ha,rfl⟩
  exact hh ha

end CFSG.Quasithin.Chapter14.Section06

namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory Stellmacher
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Normalizer control yields the source radical, T₀, and central-involution conclusions. -/
theorem source_paired_point_radical
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hpairIndex : (((T : Subgroup G) ⊓ I).relIndex Λ) = 2) :
    let Rz := (I ⊓ Mc).pCoreIn 2
    let T0 := suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u
    elementaryAbelianMaxJ Rz = I.pCoreIn 2 ∧
      (Mc ⊓ normalizer (Rz : Set G)).pCoreIn 2 = Rz ∧
      Mc.pCoreIn 2 ≤ Rz ∧ (T : Subgroup G) ⊓ I = T0 ∧
      omegaOneCenterAmbient Rz ≤ omegaOneCenterAmbient (Mc.pCoreIn 2) := by
  let R := (T : Subgroup G) ⊓ I
  let B := I ⊓ Mc
  let W := B.pCoreIn 2
  let Q := I.pCoreIn 2
  let N := normalizer (Q : Set G)
  have hJ : elementaryAbelianMaxJ W = Q := source_paired_point_thompson
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi hpairIndex
  have hQR : Q ≤ R := (pCoreIn_le_sylow I c.sylow).trans_eq c.sylow_image
  have hQI : I ≤ normalizer (Q : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hQne : Q ≠ ⊥ := hI.1.1.1
  have hN := (source_lemma_14_6_9_normalizers T
    ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) M Mc I hI.1 Q hQne hQR hQI).1
  have hNT := (source_lemma_14_6_9_normalizers T
    ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) M Mc I hI.1 Q hQne hQR hQI).2.1
  obtain ⟨PN,hPN⟩ := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal N hN.1).1
  have hPNR : (PN : Subgroup N).map N.subtype = R := hPN.trans hNT
  obtain ⟨⟨z,hz,h115⟩,_,_⟩ := source_lemma_14_6_7_initial hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI.1.1 c.sylow c.sylow_image
  have hRB : R ≤ B := le_inf inf_le_right (by
    intro r hr
    exact h115.mem_HeOver.2.2 (c.sylow_image.symm ▸ hr))
  have hWn : B ≤ normalizer (W : Set G) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hNWN : normalizer (W : Set G) ≤ N := by
    change normalizer (W : Set G) ≤ normalizer (Q : Set G)
    rw [←hJ]
    exact normalizer_le_normalizer_elementaryAbelianMaxJ W
  have hBN : B ≤ N := hWn.trans hNWN
  let NW := Mc ⊓ normalizer (W : Set G)
  have hNWN' : NW ≤ N := inf_le_right.trans hNWN
  have hBNW : B ≤ NW := le_inf inf_le_right hWn
  obtain ⟨PW,hPW⟩ := PN.exists_map_subtype_eq_of_le hNWN'
    (by rw [hPNR]; exact hRB.trans hBNW)
  have hrad : (Mc ⊓ normalizer (W : Set G)).pCoreIn 2 = W := by
    have hh := pCoreIn_normalizer_eq_of_sylow_le PW hBNW
      (by rw [hPW,hPNR]; exact hRB)
    have he : NW ⊓ normalizer (B.pCoreIn 2 : Set G) = NW :=
      inf_eq_left.mpr inf_le_right
    rw [he] at hh
    exact hh
  have hWQ : Mc.pCoreIn 2 ≤ W := ambient_core_le_radical Mc W
    ((pCoreIn_le 2 B).trans inf_le_right) (isPGroup_pCoreIn 2 B) hrad.le
  obtain ⟨PB,hPB⟩ := c.sylow.exists_map_subtype_eq_of_le
    (show B ≤ I from inf_le_left) (by rw [c.sylow_image]; exact hRB)
  have hWR : W ≤ R := (pCoreIn_le_sylow B PB).trans_eq (hPB.trans c.sylow_image)
  have hR0 := source_suitable_intersection_le_quotientCentralizer hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1.1
  have hdata := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct
  have hReq : R = suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u := by
    apply le_antisymm hR0
    rw [hdata.2.2.1]
    exact sup_le (hWQ.trans hWR) (le_inf inf_le_left hI.1.1.2.1)
  have hΩ : omegaOneCenterAmbient W ≤ omegaOneCenterAmbient (Mc.pCoreIn 2) := by
    intro w hw
    obtain ⟨hwW,hw2,hwC⟩ := (mem_omegaOneCenterAmbient_iff W w).mp hw
    have hwQ : w ∈ Mc.pCoreIn 2 := h115.mem_HeOver.1
      ⟨(pCoreIn_le 2 B hwW).2,centralizer_le hWQ hwC⟩
    exact (mem_omegaOneCenterAmbient_iff _ w).mpr ⟨hwQ,hw2,centralizer_le hWQ hwC⟩
  exact ⟨hJ,hrad,hWQ,hReq,hΩ⟩
end CFSG.Quasithin.Chapter14.Section06
