module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalGraph
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import CFSG.Quasithin.ChapterE.Section05.RankBridge
public import Theory.GroupTheory.IndexTwoNormalizer
public import Theory.GroupTheory.SubgroupCoverTransport
public import Theory.GroupTheory.ConjugacyFamilySpan

/-!
# The first index-two neighbor in the source 6.2.8 graph

Generation parameter one supplies an escaping E-member for the conjugacy
family of a moving elementary subgroup. The E.1.4 normal-closure identity
forces it to move a conjugate of the seed. The E.1.5 bound on its original
two-core quotient then gives normalizer index two. Sylow conjugacy and the
unique maximal overgroup permit this argument for every moving elementary
subgroup of the actual H-star vertex.

Transport the original H-conjugate closure across the normalized critical
endpoint. Its escape from the vertex core follows from the critical ball,
so the preceding argument supplies an endpoint neighbor alpha. Selecting a
moving seed from the original closure then supplies beta, also with index
two. Both statements use the literal graph modules and ambient inclusions.

These are the first two neighbor selections of 6.2.8. The subsequent field
planes, reverse neighbor and non-two conjugate pair remain necessary for
the terminal core escape; no LocalAnalysis record is assumed or produced.
Source: Aschbacher--Smith, 6.2.8, printed pp.684--685, F.7.13(1), p.314,
and E.1.4--6, pp.209--210.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterE
variable {G : Type*} [Group G] [Finite G]

private theorem member_neighbor (S A K B : Subgroup G)
    (hK : IsEMemberAt 1 S A K)
    (hSB : S ≤ normalizer (B : Set G))
    (hKB : ¬ K ≤ normalizer (B : Set G)) :
    ∃ k ∈ K, (A ⊓ normalizer (B.map (MulAut.conj k).toMonoidHom : Set G)).relIndex A = 2 := by
  let a := A.subgroupOf K
  let Q := (pCore 2 K).map K.subtype
  have hAK : A ≤ K := hK.1.2.2.1
  obtain ⟨P,hP⟩ := hK.1.2.2.2.2.1
  have hgen : normalClosure (a : Set K) ⊔ (P : Subgroup K) = ⊤ :=
    top_unique (by rw [←pResidual_sup_sylow_eq_top P]; exact sup_le_sup_right hK.1.residual_le_normalClosure _)
  have hmove : ∃ k ∈ K, ¬ A ≤ normalizer (B.map (MulAut.conj k).toMonoidHom : Set G) := by
    by_contra hh
    have hall : ∀ k ∈ K, A ≤ normalizer (B.map (MulAut.conj k).toMonoidHom : Set G) := by
      simpa only [not_exists,not_and,not_not] using hh
    let N := (normalizer (B : Set G)).subgroupOf K
    have haN : a ≤ N.normalCore := by
      intro x hx k
      have hn := hall (k : G)⁻¹ (K.inv_mem k.property) hx
      have hm := mem_map_of_mem (MulAut.conj (k : G)).toMonoidHom hn
      rw [←map_equiv_normalizer_eq] at hm
      have hb := fusion_map_conj_inverse (normalizer (B : Set G)) (k : G)⁻¹
      simp only [inv_inv] at hb
      rw [hb] at hm
      exact hm
    have hcl : normalClosure (a : Set K) ≤ N :=
      (normalClosure_le_normal haN).trans N.normalCore_le
    have hPN : (P : Subgroup K) ≤ N := by rw [hP]; exact fun _ hx => hSB hx
    have htop : (⊤ : Subgroup K) ≤ N := hgen ▸ sup_le hcl hPN
    exact hKB (fun x hx => htop (mem_top (⟨x,hx⟩ : K)))
  obtain ⟨k,hk,hmove⟩ := hmove
  let C := normalizer (B.map (MulAut.conj k).toMonoidHom : Set G)
  have hQB : Q ≤ normalizer (B : Set G) := by
    rintro _ ⟨q,hq,rfl⟩
    have hp := pCore_isPGroup.le_sylow_of_normal P hq
    rw [hP] at hp
    exact hSB hp
  have hQC : Q ≤ C := by
    intro q hq
    have hq' : k⁻¹*q*k ∈ Q := by
      obtain ⟨v,hv,rfl⟩ := hq
      let w : K := ⟨k,hk⟩
      exact ⟨w⁻¹*v*w, by
        change w⁻¹*v*w ∈ pCore 2 K
        simpa only [inv_inv] using
        (inferInstance : (pCore 2 K).Normal).conj_mem v hv w⁻¹, rfl⟩
    have hm := mem_map_of_mem (MulAut.conj k).toMonoidHom (hQB hq')
    rw [map_equiv_normalizer_eq] at hm
    simpa [C,MulAut.conj_apply,mul_assoc] using hm
  let _ : IsElementaryAbelian 2 A := hK.1.1
  have hiPow : (A ⊓ Q).relIndex A = 2 ^ ChapterE.subgroupCorank A (A ⊓ Q) := by
    rw [ChapterE.subgroupCorank_eq_quotient_finrank]
    exact A.relIndex_eq_two_pow_quotient_finrank (A ⊓ Q)
  have hib : (A ⊓ Q).relIndex A ≤ 2 := by
    rw [hiPow]
    exact (Nat.pow_le_pow_right (by decide) hK.core_rank_le).trans_eq (by decide)
  have hd : (A ⊓ C).relIndex A ∣ (A ⊓ Q).relIndex A :=
    relIndex_dvd_of_le_left A (inf_le_inf_left A hQC)
  have hi : (A ⊓ C).relIndex A ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero ((A ⊓ Q).subgroupOf A).index_ne_zero_of_finite) hd).trans hib
  have hpos : 0 < (A ⊓ C).relIndex A := Nat.pos_of_ne_zero ((A ⊓ C).subgroupOf A).index_ne_zero_of_finite
  have hne : (A ⊓ C).relIndex A ≠ 1 := fun hh => hmove ((relIndex_eq_one.mp hh).trans inf_le_right)
  refine ⟨k,hk,?_⟩
  change (A ⊓ C).relIndex A = 2
  omega

private theorem rank_one_neighbor_in_sylow
    (T : Sylow 2 G) (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hn : generationParameter G = 1) (hAT : A ≤ (T : Subgroup G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hproper : normalizer (B : Set G) ≠ ⊤)
    (hunique : ∀ N : Subgroup G, (T : Subgroup G) ≤ N → N ≠ ⊤ →
      N ≤ normalizer (B : Set G))
    (hcore : ¬ A ≤ pCore 2 G) :
    ∃ g : G, (A ⊓ normalizer (B.map (MulAut.conj g).toMonoidHom : Set G)).relIndex A = 2 := by
  let Ω : Set (Subgroup G) := {A' | ∃ g : G, A.map (MulAut.conj g).toMonoidHom = A'}
  have hΩ : IsElementaryFamily Ω := by
    constructor
    · rintro _ ⟨g,rfl⟩; exact IsElementaryAbelian.map _
    · rintro g _ ⟨c,rfl⟩
      exact ⟨g*c,(fusion_map_conj_mul A g c).symm⟩
  let W := weakClosure (T : Subgroup G) Ω
  have hAW : A ≤ W := le_sSup ⟨⟨1,by rw [show (MulAut.conj (1:G)).toMonoidHom = MonoidHom.id G from by ext x; simp, map_id]⟩,hAT⟩
  have hTN : (T : Subgroup G) ≤ normalizer (W : Set G) :=
    T.toSubgroup.le_normalizer.trans
      (SubgroupFamily.normalizer_le_span_normalizer (fun A' hA' g => hΩ.2 g A' hA') _)
  have hWN : normalizer (W : Set G) ≠ ⊤ := by
    intro he
    let _ : W.Normal := normalizer_eq_top_iff.mp he
    exact hcore (hAW.trans (le_sSup ⟨inferInstance,T.isPGroup'.to_le (weakClosure_le _ _)⟩))
  obtain ⟨A',⟨g,rfl⟩,hA'T,K,hK,hKN⟩ :=
    exists_rankOne_member_of_parameter_eq_one hn T Ω hΩ _ hproper (hunique _ hTN hWN)
  obtain ⟨k,hk,hi⟩ := member_neighbor (T : Subgroup G) _ K B hK hTB hKN
  have hm := relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
    (A.map (MulAut.conj g).toMonoidHom ⊓ normalizer (B.map (MulAut.conj k).toMonoidHom : Set G))
    (A.map (MulAut.conj g).toMonoidHom) (MulAut.conj g⁻¹).injective
  rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective,fusion_map_conj_inverse,
    map_equiv_normalizer_eq,fusion_map_conj_mul,hi] at hm
  exact ⟨g⁻¹*k,hm⟩

/-- The E-generation neighbor step in 6.2.8. A moving elementary subgroup
of the original vertex group has an index-two normalizer on some conjugate
of its seed, using the unique maximal overgroup of the original Sylow. -/
theorem local_rank_one_neighbor
    (T : Sylow 2 G) (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hn : generationParameter G = 1)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hproper : normalizer (B : Set G) ≠ ⊤)
    (hunique : ∀ N : Subgroup G, (T : Subgroup G) ≤ N → N ≠ ⊤ →
      N ≤ normalizer (B : Set G))
    (hcore : ¬ A ≤ pCore 2 G) :
    ∃ g : G, (A ⊓ normalizer (B.map (MulAut.conj g).toMonoidHom : Set G)).relIndex A = 2 := by
  obtain ⟨P,hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq G P T
  let A' := A.map (MulAut.conj c).toMonoidHom
  let _ : IsElementaryAbelian 2 A' := IsElementaryAbelian.map _
  have hA'T : A' ≤ (T : Subgroup G) := by
    rw [←hc]
    exact map_mono hAP
  have hncore : ¬ A' ≤ pCore 2 G := by
    intro he
    have hh := map_mono (f := (MulAut.conj c⁻¹).toMonoidHom) he
    rw [fusion_map_conj_inverse,pCore_map_iso] at hh
    exact hcore hh
  obtain ⟨g,hi⟩ := rank_one_neighbor_in_sylow T A' B hn hA'T hTB hproper hunique hncore
  have hm := relIndex_map_map_of_injective (f := (MulAut.conj c⁻¹).toMonoidHom)
    (A' ⊓ normalizer (B.map (MulAut.conj g).toMonoidHom : Set G)) A' (MulAut.conj c⁻¹).injective
  rw [map_inf _ _ _ (MulAut.conj c⁻¹).injective,show A'.map (MulAut.conj c⁻¹).toMonoidHom = A from fusion_map_conj_inverse A c,
    map_equiv_normalizer_eq,fusion_map_conj_mul,hi] at hm
  exact ⟨c⁻¹*g,hm⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterE
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- Apply the neighbor step within the original H-star subgroup. -/
theorem local_hstar_index_two_neighbor
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hN : H ⊓ normalizer (layer L R : Set G) = H ⊓ M)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAH : A ≤ H)
    (hcore : ¬ A ≤ H.pCoreIn 2) :
    ∃ g ∈ H, (A ⊓ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex A = 2 := by
  have hTH := hH.1.1.2
  have hBH := h.layer_le_T.trans hTH
  let S := T.subtype hTH
  let a := A.subgroupOf H
  let b := (layer L R).subgroupOf H
  let _ : IsElementaryAbelian 2 a := IsElementaryAbelian.subgroupOf hAH
  have hN' : normalizer (b : Set H) = M.subgroupOf H := by
    rw [←subgroupOf_normalizer_eq hBH]
    ext x
    exact ⟨fun hx => (hN.le ⟨x.property,hx⟩).2,fun hx => (hN.ge ⟨x.property,hx⟩).2⟩
  have hp : normalizer (b : Set H) ≠ ⊤ := by
    rw [hN']
    exact fun he => hH.1.2 (subgroupOf_eq_top.mp he)
  have hu : ∀ N : Subgroup H, (S : Subgroup H) ≤ N → N ≠ ⊤ → N ≤ normalizer (b : Set H) := by
    intro N hSN hNtop
    obtain ⟨X,hNX,hX⟩ := exists_le_covBy_of_lt (lt_top_iff_ne_top.mpr hNtop)
    have hcov : X.map H.subtype ⋖ H := by
      simpa only [←MonoidHom.range_eq_map,range_subtype] using
        (covBy_map_subtype_iff H X ⊤).mpr hX
    have hTX : (T : Subgroup G) ≤ X.map H.subtype := by
      rw [←map_subgroupOf_eq_of_le hTH]
      exact map_mono (hSN.trans hNX)
    have he := (Chapter3.HStar.unique_maximal T h.sylow_le hH).2.2 _ hTX hcov
    rw [hN']
    intro x hx
    exact (he.le (mem_map_of_mem H.subtype (hNX hx))).2
  have haCore : ¬ a ≤ pCore 2 H := by
    intro hh
    exact hcore (by simpa only [a,pCoreIn,map_subgroupOf_eq_of_le hAH] using map_mono (f := H.subtype) hh)
  obtain ⟨g,hi⟩ := local_rank_one_neighbor S a b (h.generation_one H hH)
    (by rw [←subgroupOf_normalizer_eq hBH]; exact fun _ hx => h.sylow_normalizes_layer hx)
    hp hu haCore
  have he : (b.map (MulAut.conj g).toMonoidHom).map H.subtype =
      (layer L R).map (MulAut.conj (g : G)).toMonoidHom := by
    rw [map_map]
    have he : H.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g:G)).toMonoidHom.comp H.subtype := rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hBH]
  have hbH : (layer L R).map (MulAut.conj (g:G)).toMonoidHom ≤ H := he ▸ map_subtype_le _
  have hb' : b.map (MulAut.conj g).toMonoidHom =
      ((layer L R).map (MulAut.conj (g:G)).toMonoidHom).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [he,map_subgroupOf_eq_of_le hbH]
  have hm := relIndex_map_map_of_injective
    (a ⊓ normalizer (b.map (MulAut.conj g).toMonoidHom : Set H)) a H.subtype_injective
  rw [hi,map_inf _ _ _ H.subtype_injective,map_subgroupOf_eq_of_le hAH,hb',
    ←subgroupOf_normalizer_eq hbH,subgroupOf_map_subtype] at hm
  have hh : A ⊓ (normalizer ((layer L R).map (MulAut.conj (g:G)).toMonoidHom : Set G) ⊓ H) =
      A ⊓ normalizer ((layer L R).map (MulAut.conj (g:G)).toMonoidHom : Set G) := by
    exact le_antisymm (inf_le_inf_left _ inf_le_left)
      (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hAH)))
  rw [hh] at hm
  exact ⟨g,g.property,hm⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition


namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterF.Section07.Track
open CFSG.Quasithin.ChapterF.Section07.CriticalPairs
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- The first application of F.7.13 in source 6.2.8, on the actual LT--H
coset graph: its elementary H-closure moves an endpoint neighbor with
normalizer of index two. All E-generation and maximality inputs are
supplied by the original H-star subgroup. -/
theorem local_graph_index_two_neighbor
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hN : H ⊓ normalizer (layer L R : Set G) = H ⊓ M)
    (hcore : layer L R ≤ H.pCoreIn 2) :
    let K := (L ⊔ (T : Subgroup G)) ⊔ H
    let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
      else (L ⊔ (T : Subgroup G)).subgroupOf K
    ∃ (D : SourceSetup F) (hne : D.V ≠ ⊥),
      D.seed.map K.subtype = layer L R ∧ Odd (D.track hne) ∧ 3 ≤ D.track hne ∧
      ∃ (e : NormalizedEndpoint D hne) (α : Vertex F),
        (graph F).Adj e.vertex α ∧
        (((vertexModule F D.seed (base F true)).map K.subtype) ⊓
          normalizer ((firstModule F D.seed α).map K.subtype : Set G)).relIndex
            ((vertexModule F D.seed (base F true)).map K.subtype) = 2 := by
  let K := (L ⊔ (T : Subgroup G)) ⊔ H
  let F : Bool → Subgroup K := fun i => if i then H.subgroupOf K
    else (L ⊔ (T : Subgroup G)).subgroupOf K
  obtain ⟨D,hne,hseed,_⟩ := local_graph_setup h (hnatural.1 ▸ hnatural.2.1)
    hunique hH.1.1.2 hH.1.2
  have hodd := local_graph_track_odd h hnatural hE hfactor D hne hseed
  have htrue : (F true).map K.subtype = H := map_subgroupOf_eq_of_le le_sup_right
  have hcore' : D.seed ≤ (F true).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective K.subtype_injective).mp
    rw [map_pCoreIn_of_injective 2 _ _ K.subtype_injective,htrue,hseed]
    exact hcore
  have hgt := Completion.one_lt_track_of_true_core F D hne hcore'
  have hb : 3 ≤ D.track hne := by obtain ⟨k,hk⟩ := hodd; omega
  obtain ⟨e⟩ := NormalizedEndpoint.nonempty (D := D) (hne := hne) hodd
  let U := vertexModule F D.seed (base F true)
  let A0 := U.map (MulAut.conj (e:K)⁻¹).toMonoidHom
  let A := A0.map K.subtype
  have hU : IsElementaryAbelian 2 U := by
    rw [show U = vertexModule F D.seed (base F true) from rfl,
      second_base_module_eq_conjugate_join F D.seed D.seed_normalized]
    exact Completion.conjugate_join_elementary_of_odd F D hne hcore' hodd
  let _ := hU
  let _ : IsElementaryAbelian 2 A0 := IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hA0 : A0 ≤ F true := by
    have hh := map_mono (f := (MulAut.conj (e:K)⁻¹).toMonoidHom) (e.reverse_module_le hb)
    rw [stabilizer_translate,fusion_map_conj_inverse] at hh
    have hs : stabilizer F (base F true) = F true := Subgroup.CosetGeometry.stabilizer_base F true
    rw [hs] at hh
    exact hh
  have hAH : A ≤ H := (map_mono hA0).trans_eq htrue
  have hAU : A0.map (MulAut.conj (e:K)).toMonoidHom = U := by
    simpa only [A0,inv_inv] using fusion_map_conj_inverse U (e:K)⁻¹
  have hseedU : D.seed ≤ U := by
    have hh := firstModule_le_vertexModule_of_adj F D.seed (v := base F true)
      (w := base F false) rfl ⟨by change true ≠ false; decide,Subgroup.CosetGeometry.incident_base F true false⟩
    rwa [firstModule_base F D.seed D.seed_normalized] at hh
  have hAC : ¬ A ≤ H.pCoreIn 2 := by
    intro hh
    have hh' : A0 ≤ (F true).pCoreIn 2 := by
      apply (map_le_map_iff_of_injective K.subtype_injective).mp
      rw [map_pCoreIn_of_injective 2 _ _ K.subtype_injective,htrue]
      exact hh
    have hc := map_mono (f := (MulAut.conj (e:K)).toMonoidHom)
      (hh'.trans (Completion.base_core_le_kernel F D true))
    rw [hAU,←ballKernel_translate] at hc
    exact e.property.2.2 (hseedU.trans hc)
  obtain ⟨g,hg,hi⟩ := local_hstar_index_two_neighbor h hH hN A hAH hAC
  let gK : K := ⟨g,(show H ≤ K from le_sup_right) hg⟩
  let α := (e:K) • (gK • base F false)
  have hgfix : gK • base F true = base F true := by
    have hs : stabilizer F (base F true) = F true := Subgroup.CosetGeometry.stabilizer_base F true
    have hh : gK ∈ stabilizer F (base F true) := hs.symm ▸ (show gK ∈ F true from hg)
    exact hh
  have hadj : (graph F).Adj e.vertex α := by
    apply (Subgroup.CosetGeometry.translationGraphIso F (e:K)).map_rel_iff.mpr
    have hh := (Subgroup.CosetGeometry.translationGraphIso F gK).map_rel_iff.mpr
      (show (graph F).Adj (base F true) (base F false) from
        ⟨by change true ≠ false; decide,Subgroup.CosetGeometry.incident_base F true false⟩)
    simpa only [Subgroup.CosetGeometry.translationGraphIso_apply,hgfix] using hh
  have hAm : A.map (MulAut.conj (e.val:G)).toMonoidHom = U.map K.subtype := by
    change (A0.map K.subtype).map _ = _
    rw [map_map]
    have he : (MulAut.conj (e.val:G)).toMonoidHom.comp K.subtype =
        K.subtype.comp (MulAut.conj (e:K)).toMonoidHom := rfl
    rw [he,←map_map,hAU]
  have hα : (firstModule F D.seed α).map K.subtype =
      (layer L R).map (MulAut.conj ((e.val:G)*g)).toMonoidHom := by
    rw [show α = ((e:K)*gK) • base F false from (mul_smul _ _ _).symm,
      firstModule_translate_base F D.seed D.seed_normalized,map_map]
    have he : K.subtype.comp (MulAut.conj ((e:K)*gK)).toMonoidHom =
        (MulAut.conj ((e.val:G)*g)).toMonoidHom.comp K.subtype := rfl
    rw [he,←map_map,hseed]
  have hm := relIndex_map_map_of_injective (f := (MulAut.conj (e.val:G)).toMonoidHom)
    (A ⊓ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)) A
      (MulAut.conj (e.val:G)).injective
  rw [map_inf _ _ _ (MulAut.conj (e.val:G)).injective,hAm,map_equiv_normalizer_eq,
    fusion_map_conj_mul,hi,←hα] at hm
  exact ⟨D,hne,hseed,hodd,hb,e,α,hadj,hm⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition


namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterF.Section07.Track
open CFSG.Quasithin.ChapterF.Section07.CriticalPairs
open Subgroup.CosetGeometry.RankTwo
variable {G K : Type*} [Group G] [Group K]

/-- An index-two moving closure has an actual seed neighbor with that same
index. This selects beta in the next paragraph of source 6.2.8; it does
not assume an index bound on a particular constituent. -/
theorem local_graph_select_moving_seed (F : Bool → Subgroup K) (D : SourceSetup F)
    (f : K →* G) (α : Vertex F)
    (hi : (((vertexModule F D.seed (base F true)).map f) ⊓
      normalizer ((firstModule F D.seed α).map f : Set G)).relIndex
        ((vertexModule F D.seed (base F true)).map f) = 2) :
    ∃ β : Vertex F, (graph F).Adj (base F true) β ∧
      (((firstModule F D.seed β).map f) ⊓
        normalizer ((firstModule F D.seed α).map f : Set G)).relIndex
          ((firstModule F D.seed β).map f) = 2 := by
  let U := (vertexModule F D.seed (base F true)).map f
  let A := (firstModule F D.seed α).map f
  have hm : ¬ U ≤ normalizer (A : Set G) := by
    intro hh
    have he := relIndex_eq_one.mpr (show U ≤ U ⊓ normalizer (A : Set G) from le_inf le_rfl hh)
    rw [hi] at he
    omega
  have hex : ∃ β : Vertex F, (graph F).Adj (base F true) β ∧
      ¬ (firstModule F D.seed β).map f ≤ normalizer (A : Set G) := by
    by_contra hh
    apply hm
    apply map_le_iff_le_comap.mpr
    rw [vertexModule_second F D.seed rfl]
    refine iSup_le fun β => iSup_le fun hβ => ?_
    apply map_le_iff_le_comap.mp
    exact Classical.byContradiction (fun hn => hh ⟨β,hβ,hn⟩)
  obtain ⟨β,hβ,hmβ⟩ := hex
  have hβU : (firstModule F D.seed β).map f ≤ U :=
    map_mono (firstModule_le_vertexModule_of_adj F D.seed rfl hβ)
  exact ⟨β,hβ,normalizer_relIndex_eq_two_of_index_two_overgroup _ U
    (U ⊓ normalizer (A : Set G)) A hβU hi inf_le_right
      (SetLike.not_le_iff_exists.mp hmβ)⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
