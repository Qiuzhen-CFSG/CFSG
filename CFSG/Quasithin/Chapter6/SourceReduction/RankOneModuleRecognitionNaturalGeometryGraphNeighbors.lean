module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryGraphEndpoints
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import Theory.GroupTheory.SolvableRadical.TwoClosedKernel
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.ConjugacyFamilySpan
public import Mathlib.GroupTheory.Schreier

/-!
# Index-two neighbors in the odd escaping graph

E-generation at parameter one and the unique maximal Sylow overgroup
produce a conjugate with an index-two normalizer intersection. In the
component E-member case, the two-closed radical has the same kernel on
the elementary actor as the two-core; hence the literal E.1.5 quotient
rank supplies the required bound. Normal generation supplies the moving
conjugate, without an assumption about its existence.

The critical endpoint puts the backward H-closure outside O₂(H). Applying
the selection theorem in H and transporting through its actual inclusion
constructs the neighboring conjugate of the natural layer. The original
global-s bound shows that its index-two normalizer acts nontrivially.

This establishes the first neighbor and nontrivial commutator in 6.1.19.
The commutator-line identification, reverse neighbor and parameter reduction,
nonabelianness, initial action and final 6.1.27 assembly remain with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, F.7.13(1), printed p.314, and 6.1.19,
printed pp.673–675. The local generation argument uses E.1.4–6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph
variable {G : Type*} [Group G] [Finite G]

private theorem core_image_card_le_two {T A K : Subgroup G}
    (h : IsEMemberAt 1 T A K) :
    Nat.card ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≤ 2 := by
  let := h.1.1
  let : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf h.1.2.2.1
  have hr : Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≤ 1 := by
    rcases h.2 with ho | hc
    · exact ho.2
    · rw [← rank_quotientImage_eq_of_inf_eq _ _ _
        (inf_solvableRadical_eq_inf_pCore (A.subgroupOf K)
          (IsElementaryAbelian.isPGroup 2 (A.subgroupOf K)) hc.1.1)]
      exact hc.2
  let a := (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))
  let : IsElementaryAbelian 2 a := IsElementaryAbelian.map _
  let : CommGroup a := IsMulCommutative.instCommGroup
  have hdvd : Nat.card a ∣ 2 ^ Group.rank a := card_dvd_exponent_pow_rank' a
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 a))
  exact (Nat.le_of_dvd (by positivity) hdvd).trans
    (by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr)

private theorem core_relIndex_le_two {T A K : Subgroup G}
    (h : IsEMemberAt 1 T A K) : (K.pCoreIn 2).relIndex A ≤ 2 := by
  have he : (K.pCoreIn 2).relIndex A =
      (pCore 2 K).relIndex (A.subgroupOf K) := by
    have hh := relIndex_map_map_of_injective (pCore 2 K) (A.subgroupOf K) K.subtype_injective
    rwa [map_subgroupOf_eq_of_le h.1.2.2.1] at hh
  rw [he]
  have hh := relIndex_ker (A.subgroupOf K) (QuotientGroup.mk' (pCore 2 K))
  rw [QuotientGroup.ker_mk'] at hh
  rw [hh]
  exact core_image_card_le_two h

private theorem member_conjugate_not_le {T A K M : Subgroup G}
    (h : IsEMember T A K) (hTM : T ≤ M) (hKM : ¬ K ≤ M) :
    ∃ k : K, ¬ A.map (MulAut.conj (k : G)).toMonoidHom ≤ M := by
  by_contra! hn
  have hspan : conjugateSpanBy A K ≤ M := by
    rw [conjugateSpanBy_eq_iSup_conj]
    exact iSup_le hn
  obtain ⟨P,hP⟩ := h.2.2.2.2.1
  apply hKM
  have hr : (pResidual 2 K).map K.subtype ≤ M := by
    have hh := map_mono (f := K.subtype) h.residual_le_normalClosure
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy _ _ h.2.2.1,
      map_subgroupOf_eq_of_le (conjugateSpanBy_le h.2.2.1 K.le_normalizer)] at hh
    exact hh.trans hspan
  have hp : (P : Subgroup K).map K.subtype ≤ M := by
    rw [hP,subgroupOf_map_subtype]
    exact inf_le_left.trans hTM
  have ht := congrArg (Subgroup.map K.subtype) (pResidual_sup_sylow_eq_top P)
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at ht
  exact ht ▸ sup_le hr hp

private theorem member_index_two_conjugate {T A K M : Subgroup G}
    (h : IsEMemberAt 1 T A K) (hTM : T ≤ M) (hKM : ¬ K ≤ M) :
    ∃ k : K, (M.map (MulAut.conj (k : G)).toMonoidHom).relIndex A = 2 := by
  obtain ⟨k,hk⟩ := member_conjugate_not_le h.1 hTM hKM
  have hcore : K.pCoreIn 2 ≤ M := by
    obtain ⟨P,hP⟩ := h.1.2.2.2.2.1
    have hh := map_mono (f := K.subtype) (pCore_isPGroup.le_sylow_of_normal P)
    rw [hP,subgroupOf_map_subtype] at hh
    exact hh.trans (inf_le_left.trans hTM)
  have hn : K ≤ normalizer (K.pCoreIn 2 : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hc : K.pCoreIn 2 ≤ M.map (MulAut.conj (k : G)⁻¹).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj (k : G)⁻¹).toMonoidHom) hcore
    have he : (K.pCoreIn 2).map (MulAut.conj (k : G)⁻¹).toMonoidHom = K.pCoreIn 2 :=
      mem_normalizer_iff_map_conj_eq.mp (hn (K.inv_mem k.property))
    rwa [he] at hh
  have hd := relIndex_dvd_of_le_left A hc
  have hl : (M.map (MulAut.conj (k : G)⁻¹).toMonoidHom).relIndex A ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero ((K.pCoreIn 2).subgroupOf A).index_ne_zero_of_finite) hd).trans (core_relIndex_le_two h)
  have hnot : (M.map (MulAut.conj (k : G)⁻¹).toMonoidHom).relIndex A ≠ 1 := by
    intro he
    apply hk
    have hh := map_mono (f := (MulAut.conj (k : G)).toMonoidHom) (relIndex_eq_one.mp he)
    have hid : (MulAut.conj (k : G)).toMonoidHom.comp
        (MulAut.conj (k : G)⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rwa [map_map,hid,Subgroup.map_id] at hh
  refine ⟨k⁻¹,?_⟩
  have hpos : 0 < (M.map (MulAut.conj (k : G)⁻¹).toMonoidHom).relIndex A :=
    Nat.pos_of_ne_zero ((M.map (MulAut.conj (k : G)⁻¹).toMonoidHom).subgroupOf A).index_ne_zero_of_finite
  change (M.map (MulAut.conj (k : G)⁻¹).toMonoidHom).relIndex A = 2
  omega

omit [Finite G] in
private theorem conj_twice (B : Subgroup G) (a b : G) :
    (B.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      B.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

omit [Finite G] in
private theorem conj_one (B : Subgroup G) :
    B.map (MulAut.conj (1 : G)).toMonoidHom = B := by
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [hid,Subgroup.map_id]

/-- The index-two neighbor argument of F.7.13(1), in the local vertex group.
The unique maximal Sylow overgroup and generation parameter one force an
index-two intersection with a conjugate of that overgroup for every
non-core elementary abelian subgroup. -/
theorem index_two_conjugate_of_unique_maximal
    (S : Sylow 2 G) (M A : Subgroup G)
    (hSM : (S : Subgroup G) ≤ M) (hM : M ≠ ⊤)
    (hunique : ∀ X : Subgroup G, (S : Subgroup G) ≤ X → X ≠ ⊤ → X ≤ M)
    (hgen : generationParameter G = 1)
    (hA : IsElementaryAbelian 2 A) (hcore : ¬ A ≤ pCore 2 G) :
    ∃ g : G, (M.map (MulAut.conj g).toMonoidHom).relIndex A = 2 := by
  let Ω : Set (Subgroup G) := {B | ∃ g : G, B = A.map (MulAut.conj g).toMonoidHom}
  let := hA
  have hΩ : IsElementaryFamily Ω := by
    refine ⟨?_,?_⟩
    · rintro B ⟨g,rfl⟩
      exact IsElementaryAbelian.map _
    · rintro g B ⟨b,rfl⟩
      exact ⟨g * b,conj_twice A b g⟩
  let W := weakClosure (S : Subgroup G) Ω
  have hSW : (S : Subgroup G) ≤ normalizer (W : Set G) :=
    (S : Subgroup G).le_normalizer.trans
      (SubgroupFamily.normalizer_le_span_normalizer (fun B hB g => hΩ.2 g B hB) _)
  have hproper : normalizer (W : Set G) ≠ ⊤ := by
    intro he
    let : W.Normal := normalizer_eq_top_iff.mp he
    have hWC : W ≤ pCore 2 G := le_sSup ⟨inferInstance,
      S.isPGroup'.to_le (weakClosure_le _ _)⟩
    obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
    obtain ⟨s,hs⟩ := MulAction.exists_smul_eq G P S
    have hAS : A.map (MulAut.conj s).toMonoidHom ≤ (S : Subgroup G) := by
      rw [←hs]
      exact map_mono hP
    have hAW : A.map (MulAut.conj s).toMonoidHom ≤ W := le_sSup ⟨⟨s,rfl⟩,hAS⟩
    have hh := map_mono (f := (MulAut.conj s⁻¹).toMonoidHom) (hAW.trans hWC)
    have hec : (pCore 2 G).map (MulAut.conj s⁻¹).toMonoidHom = pCore 2 G :=
      mem_normalizer_iff_map_conj_eq.mp (show s⁻¹ ∈ normalizer (pCore 2 G : Set G) from
        (pCore 2 G).normalizer_eq_top ▸ mem_top _)
    rw [conj_twice,inv_mul_cancel,conj_one,hec] at hh
    exact hcore hh
  obtain ⟨B,⟨g,rfl⟩,hBS,K,hK,hKM⟩ :=
    exists_rankOne_member_of_parameter_eq_one hgen S Ω hΩ M hM
      (hunique _ hSW hproper)
  obtain ⟨k,hk⟩ := member_index_two_conjugate hK hSM hKM
  have hh := relIndex_map_map_of_injective
    (f := (MulAut.conj g⁻¹).toMonoidHom)
    (M.map (MulAut.conj (k : G)).toMonoidHom)
    (A.map (MulAut.conj g).toMonoidHom) (MulAut.conj g⁻¹).injective
  rw [hk,conj_twice,conj_twice,inv_mul_cancel,conj_one] at hh
  exact ⟨g⁻¹ * (k : G),hh⟩

open Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Section07.Track
open CFSG.Quasithin.ChapterF.Section07.CriticalPairs
namespace OddConfiguration
variable {T : Sylow 2 G} {L M R : Subgroup G}
variable (d : OddConfiguration T L M R)

private theorem closure_back_le :
    d.localClosure.map (MulAut.conj d.representative⁻¹).toMonoidHom ≤ d.H := by
  have hh := map_mono (f := (MulAut.conj d.representative⁻¹).toMonoidHom)
    d.opposite_placements.2.1
  rwa [conj_twice,inv_mul_cancel,conj_one] at hh

/-- The backward endpoint closure leaves the original vertex two-core.
Otherwise the original seed would fix the first ball of its critical endpoint. -/
theorem closure_back_not_le_core :
    ¬ d.localClosure.map (MulAut.conj d.representative⁻¹).toMonoidHom ≤ d.H.pCoreIn 2 := by
  intro hc
  let K := (L ⊔ (T : Subgroup G)) ⊔ d.H
  let F : Bool → Subgroup K := fun i => if i then d.H.subgroupOf K
    else (L ⊔ (T : Subgroup G)).subgroupOf K
  have hA := map_mono (f := (MulAut.conj d.representative).toMonoidHom) hc
  rw [conj_twice,mul_inv_cancel,conj_one] at hA
  have hmap (B : Subgroup K) :
      (B.map (MulAut.conj d.endpoint.val).toMonoidHom).map K.subtype =
        (B.map K.subtype).map (MulAut.conj d.representative).toMonoidHom := by
    rw [map_map,map_map]
    rfl
  have hC : ((F true).pCoreIn 2).map K.subtype = d.H.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ K.subtype_injective]
    change ((d.H.subgroupOf K).map K.subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le le_sup_right]
  have hh := map_mono (f := K.subtype)
    (map_mono (f := (MulAut.conj d.endpoint.val).toMonoidHom)
      (Completion.base_core_le_kernel F d.D true))
  rw [← ballKernel_translate,hmap,hC] at hh
  apply d.endpoint.property.2.2
  apply (map_le_map_iff_of_injective K.subtype_injective).mp
  rw [d.seed_map]
  exact (le_conjugateSpanBy (layer L R) d.H).trans (hA.trans hh)

private theorem all_proper_sylow_overgroups
    (X : Subgroup d.H) (hTX : ((T : Subgroup G).subgroupOf d.H) ≤ X)
    (hX : X ≠ ⊤) : X ≤ M.subgroupOf d.H := by
  have hlt : X.map d.H.subtype < d.H := by
    refine lt_of_le_of_ne (map_subtype_le _) ?_
    intro he
    apply hX
    apply map_injective d.H.subtype_injective
    simpa only [← MonoidHom.range_eq_map,range_subtype] using he
  obtain ⟨Y,hXY,hY⟩ := exists_le_covBy_of_lt hlt
  have hTY : (T : Subgroup G) ≤ Y := by
    have hh := map_mono (f := d.H.subtype) hTX
    rw [map_subgroupOf_eq_of_le d.hstar.1.1.2] at hh
    exact hh.trans hXY
  rw [d.unique_maximal Y hTY hY] at hXY
  intro x hx
  exact (hXY (mem_map_of_mem d.H.subtype hx)).2

/-- The actual odd critical configuration supplies a neighboring natural
layer whose normalizer has index two in the original H-closure. The same
ambient conjugator places this layer in the opposite endpoint closure. -/
theorem exists_index_two_neighbor
    {n : ℕ} (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n) :
    ∃ a : G, d.representative⁻¹ * a ∈ d.H ∧
      (layer L R).map (MulAut.conj a).toMonoidHom ≤
        d.localClosure.map (MulAut.conj d.representative).toMonoidHom ∧
      (Subgroup.normalizer ((layer L R).map (MulAut.conj a).toMonoidHom : Set G)).relIndex
        d.localClosure = 2 := by
  let A := d.localClosure.map (MulAut.conj d.representative⁻¹).toMonoidHom
  let S := T.subtype d.hstar.1.1.2
  let B := M.subgroupOf d.H
  have hB : B ≠ ⊤ := by
    intro he
    apply d.hstar.1.2
    intro x hx
    exact show (⟨x,hx⟩ : d.H) ∈ B from he ▸ mem_top _
  have hSB : (S : Subgroup d.H) ≤ B := fun x hx => h.sylow_le hx
  let : IsElementaryAbelian 2 d.localClosure := d.closure_elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAC : ¬ A.subgroupOf d.H ≤ pCore 2 d.H := by
    intro hh
    apply d.closure_back_not_le_core
    have hm := map_mono (f := d.H.subtype) hh
    rwa [map_subgroupOf_eq_of_le d.closure_back_le] at hm
  have hAE : IsElementaryAbelian 2 (A.subgroupOf d.H) :=
    IsElementaryAbelian.subgroupOf d.closure_back_le
  obtain ⟨k,hk⟩ := index_two_conjugate_of_unique_maximal S B (A.subgroupOf d.H)
    hSB hB (fun X hX hne => d.all_proper_sylow_overgroups X hX hne)
    d.generation hAE hAC
  have hmap (C : Subgroup d.H) :
      (C.map (MulAut.conj k).toMonoidHom).map d.H.subtype =
        (C.map d.H.subtype).map (MulAut.conj (k : G)).toMonoidHom := by
    rw [map_map,map_map]
    rfl
  have hBmap : B.map d.H.subtype = d.H ⊓ Subgroup.normalizer (layer L R : Set G) := by
    rw [d.normalizer]
    exact (subgroupOf_map_subtype M d.H).trans (inf_comm M d.H)
  have hh := relIndex_map_map_of_injective
    (B.map (MulAut.conj k).toMonoidHom) (A.subgroupOf d.H) d.H.subtype_injective
  rw [hk,hmap,hBmap,map_subgroupOf_eq_of_le d.closure_back_le] at hh
  have hn : (Subgroup.normalizer ((layer L R).map (MulAut.conj (k : G)).toMonoidHom : Set G)).relIndex A = 2 := by
    have hnorm : (d.H ⊓ Subgroup.normalizer (layer L R : Set G)).map
        (MulAut.conj (k : G)).toMonoidHom =
        d.H ⊓ Subgroup.normalizer ((layer L R).map (MulAut.conj (k : G)).toMonoidHom : Set G) := by
      rw [map_inf _ _ _ (MulAut.conj (k : G)).injective,
        map_normalizer_eq_of_bijective _ (f := (MulAut.conj (k : G)).toMonoidHom) (MulAut.conj (k : G)).bijective]
      have he : d.H.map (MulAut.conj (k : G)).toMonoidHom = d.H :=
        mem_normalizer_iff_map_conj_eq.mp (d.H.le_normalizer k.property)
      rw [he]
    rw [hnorm] at hh
    have hi : (d.H ⊓ Subgroup.normalizer ((layer L R).map (MulAut.conj (k : G)).toMonoidHom : Set G)).subgroupOf A =
        (Subgroup.normalizer ((layer L R).map (MulAut.conj (k : G)).toMonoidHom : Set G)).subgroupOf A := by
      ext x
      exact and_iff_right (d.closure_back_le x.property)
    change ((d.H ⊓ _).subgroupOf A).index = 2 at hh
    rwa [hi] at hh
  refine ⟨d.representative * (k : G),by simpa only [inv_mul_cancel_left] using k.property,?_,?_⟩
  · rw [←conj_twice]
    apply map_mono
    change _ ≤ conjugateSpanBy (layer L R) d.H
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun x : d.H => (layer L R).map (MulAut.conj (x : G)).toMonoidHom) k
  · have hi := relIndex_map_map_of_injective
      (f := (MulAut.conj d.representative).toMonoidHom)
      (Subgroup.normalizer ((layer L R).map (MulAut.conj (k : G)).toMonoidHom : Set G)) A
      (MulAut.conj d.representative).injective
    rw [hn,map_normalizer_eq_of_bijective _ (f := (MulAut.conj d.representative).toMonoidHom) (MulAut.conj d.representative).bijective,
      conj_twice] at hi
    change _ = 2 at hi
    dsimp only [A] at hi
    rwa [conj_twice,mul_inv_cancel,conj_one] at hi

/-- The neighbor uses the endpoint's actual central line. Its representative
lies in the same H-coset, and H normalizes the original line. -/
theorem neighbor_line_eq
    {n : ℕ} (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    {a : G} (ha : d.representative⁻¹ * a ∈ d.H) :
    (ZS (T : Subgroup G) L R).map (MulAut.conj a).toMonoidHom =
      (ZS (T : Subgroup G) L R).map (MulAut.conj d.representative).toMonoidHom := by
  have hn : d.H ≤ Subgroup.normalizer (ZS (T : Subgroup G) L R : Set G) :=
    d.overgroup.trans (sup_le (Subgroup.centralizer_le_normalizer _) h.sylow_normalizes_ZS)
  have he : (ZS (T : Subgroup G) L R).map
      (MulAut.conj (d.representative⁻¹ * a)).toMonoidHom = ZS (T : Subgroup G) L R :=
    mem_normalizer_iff_map_conj_eq.mp (hn ha)
  have hh := congrArg (Subgroup.map (MulAut.conj d.representative).toMonoidHom) he
  rwa [conj_twice,mul_inv_cancel_left] at hh

/-- A hyperplane of the local closure has the same two-group centralizer
as the whole closure. This uses s(G,V)>1 on each literal H-conjugate of V. -/
theorem centralizer_of_hyperplane
    {n : ℕ} (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    {B E : Subgroup G} (hB : B.relIndex d.localClosure ≤ 2)
    (hE : IsPGroup 2 E) (hc : E ≤ centralizer (B : Set G)) :
    E ≤ centralizer (d.localClosure : Set G) := by
  let := h.layer_elementary
  apply le_centralizer_iff.mpr
  change conjugateSpanBy (layer L R) d.H ≤ centralizer (E : Set G)
  rw [conjugateSpanBy_eq_iSup_conj]
  apply iSup_le
  intro k
  let C := (layer L R).map (MulAut.conj (k : G)).toMonoidHom
  have hCA : C ≤ d.localClosure := by
    change C ≤ conjugateSpanBy (layer L R) d.H
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun x : d.H => (layer L R).map (MulAut.conj (x : G)).toMonoidHom) k
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  have hi : B.relIndex C ≤ 2 :=
    (relIndex_le_of_le_right hCA (B.subgroupOf d.localClosure).index_ne_zero_of_finite).trans hB
  have hr : subgroupCorank C (C ⊓ B) ≤ 1 := by
    unfold subgroupCorank
    rw [inf_relIndex_left]
    have hh := Nat.log_mono_right hi (b := 2)
    norm_num at hh ⊢
    exact hh
  have hsC : globalS C = n := by
    rw [globalS_map_equiv (layer L R) (MulAut.conj (k : G)),hs]
  have heq := centralizer_inf_eq_of_corank_lt_globalS
    (show C ⊓ B ≤ C from inf_le_left)
    (show (subgroupCorank C (C ⊓ B) : ℕ∞) < globalS C from by
      rw [hsC]
      exact_mod_cast lt_of_le_of_lt hr h.n_gt_one) hE
  apply le_centralizer_iff.mp
  have hEB : E ≤ centralizer (C ⊓ B : Set G) := hc.trans (centralizer_le inf_le_right)
  have hh : E ≤ E ⊓ centralizer (C : Set G) := by
    rw [←heq]
    exact le_inf le_rfl hEB
  exact hh.trans inf_le_right

/-- Source 6.1.19's first chosen neighbor has an index-two normalizer
and a nontrivial commutator with that normalizer. -/
theorem exists_moving_index_two_neighbor
    {n : ℕ} (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hs : letI := h.layer_elementary; globalS (layer L R) = n) :
    ∃ a : G, let E := (layer L R).map (MulAut.conj a).toMonoidHom
      d.representative⁻¹ * a ∈ d.H ∧
      (ZS (T : Subgroup G) L R).map (MulAut.conj a).toMonoidHom =
        (ZS (T : Subgroup G) L R).map (MulAut.conj d.representative).toMonoidHom ∧
      E ≤ d.localClosure.map (MulAut.conj d.representative).toMonoidHom ∧
      (Subgroup.normalizer (E : Set G)).relIndex d.localClosure = 2 ∧
      ⁅E,d.localClosure ⊓ Subgroup.normalizer (E : Set G)⁆ ≠ ⊥ := by
  obtain ⟨a,hcoset,ha,hi⟩ := d.exists_index_two_neighbor h
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  refine ⟨a,hcoset,d.neighbor_line_eq h hcoset,ha,hi,?_⟩
  intro hz
  have hE : IsPGroup 2 E := by
    let := h.layer_elementary
    exact (IsElementaryAbelian.isPGroup 2 (layer L R)).map _
  have hc := d.centralizer_of_hyperplane h hs
    (show (d.localClosure ⊓ Subgroup.normalizer (E : Set G)).relIndex d.localClosure ≤ 2 from by
      rw [inf_relIndex_left]; exact hi.le) hE
    (commutator_eq_bot_iff_le_centralizer.mp hz)
  have hn : d.localClosure ≤ Subgroup.normalizer (E : Set G) :=
    (le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)
  have hh := relIndex_eq_one.mpr hn
  rw [hi] at hh
  norm_num at hh

end OddConfiguration

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph
