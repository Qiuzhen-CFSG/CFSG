module
public import CFSG.Quasithin.ChapterE.Section03.SourceContainment

/-!
# Rank-one E-generation through the weak centralizer

For every rank-one E-member, the elementary generator meets its two-core
in exact corank one. The same holds for every conjugate of that generator.
Its intersection therefore lies in W₁(S,V). Since C₁(S,V) is a two-group,
small-corank centralizer rigidity makes it centralize the whole conjugate.
E.1.4 then places the member's two-residual in C_H(C₁(S,V)); E-generation
and N_H(W₀(S,V)) generate the overgroup.

This supplies the i=0,j=1 case consumed in original 8.3.9, without assuming
W₁(S,V) centralizes V. Source: Aschbacher--Smith E.3.6 and E.3.19,
printed pp.232,234--235; 8.3.9, printed p.725.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.WeakCentralizerContainment
variable {G : Type*} [Group G] [Finite G]

private theorem normalClosure_centralizes_one {V S : Subgroup G} [IsElementaryAbelian 2 V]
    (hS : IsPGroup 2 S)
    {K : Type*} [Group K] [Finite K] (A : Subgroup K) [IsElementaryAbelian 2 A]
    (f : K →* G) (hf : Function.Injective f) (g : G)
    (hAg : A.map f = V.map (MulAut.conj g).toMonoidHom)
    (hcore : (pCore 2 K).map f ≤ S)
    (hcorank : subgroupCorank A (A ⊓ pCore 2 K) = 1)
    (hs : (1 : ℕ∞) < globalS V) :
    (normalClosure (A : Set K)).map f ≤ centralizer (weakCentralizer V S 1 : Set G) := by
  have hconj (k : K) :
      (A.map (f.comp (MulAut.conj k).toMonoidHom)) ≤ centralizer (weakCentralizer V S 1 : Set G) := by
    let f' := f.comp (MulAut.conj k).toMonoidHom
    have hinj : Function.Injective f' := hf.comp (MulAut.conj k).injective
    have he : A.map f' = V.map (MulAut.conj (f k * g)).toMonoidHom := by
      have hcomp : f' = (MulAut.conj (f k)).toMonoidHom.comp f := by ext x; simp [f']
      rw [hcomp, ← map_map, hAg, map_map]
      congr 1
      ext x
      simp [mul_assoc]
    have hBC : ((A ⊓ pCore 2 K).map f') ≤ S := by
      apply le_trans _ hcore
      rintro x ⟨a, ha, rfl⟩
      exact mem_map_of_mem f ((inferInstance : (pCore 2 K).Normal).conj_mem a ha.2 k)
    have hb : subgroupCorank (V.map (MulAut.conj (f k * g)).toMonoidHom)
        ((A ⊓ pCore 2 K).map f') = 1 := by
      rw [← he, subgroupCorank, relIndex_map_map_of_injective _ _ hinj]
      exact hcorank
    let W := V.map (MulAut.conj (f k * g)).toMonoidHom
    let B := (A ⊓ pCore 2 K).map f'
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
    have hBW : B ≤ W := (map_mono (f := f') (inf_le_left : A ⊓ pCore 2 K ≤ A)).trans_eq he
    have hgamma : B ∈ gamma V S 1 := by
      refine ⟨⟨f k * g,hBW,?_⟩,hBC⟩
      rw [relIndex_eq_two_pow_quotient_finrank, ←subgroupCorank_eq_quotient_finrank, hb]
    have hCB : weakCentralizer V S 1 ≤ centralizer (B : Set G) :=
      inf_le_right.trans (centralizer_le (gamma_le_weakClosure hgamma))
    have hrigid := centralizer_inf_eq_of_corank_lt_globalS hBW
      (by rw [globalS_map_equiv,hb]; exact hs)
      (hS.to_le (show weakCentralizer V S 1 ≤ S from inf_le_left))
    have hCW : weakCentralizer V S 1 ≤ centralizer (W : Set G) := by
      rw [inf_eq_left.mpr hCB] at hrigid
      exact inf_eq_left.mp hrigid.symm
    rw [he]
    exact le_centralizer_iff.mpr hCW
  apply map_le_iff_le_comap.mpr
  change Subgroup.closure (Group.conjugatesOfSet (A : Set K)) ≤ _
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨k, rfl⟩ := isConj_iff.mp hax
  exact hconj k (mem_map_of_mem _ ha)


/-- The rank-one case of E.3.19: control of N(W₀) and C(C₁) controls the overgroup. -/
theorem le_of_isEGenerated_one {V M H : Subgroup G} [IsElementaryAbelian 2 V]
    (S : Sylow 2 H) (hgen : IsEGeneratedAt 1 S)
    (hNM : normalizer (indexedWeakClosure V ((S : Subgroup H).map H.subtype) 0 : Set G) ≤ M)
    (hCV : H ⊓ centralizer
      (weakCentralizer V ((S : Subgroup H).map H.subtype) 1 : Set G) ≤ M)
    (hs : (1 : ℕ∞) < globalS V) : H ≤ M := by
  let Ω := conjugateCorankFamily V 0
  have hΩ : IsElementaryFamily Ω := by
    constructor
    · rintro A ⟨g, hAV, hi⟩
      let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
      exact IsElementaryAbelian.of_injective (Subgroup.inclusion hAV) (Subgroup.inclusion_injective _)
    · intro g A hA
      exact conjugateCorankFamily_invariant V 0 A hA g
  let ΩH := ChiefOrbit.restrictedFamily H Ω
  have hΩH : IsElementaryFamily ΩH := ChiefOrbit.restrictedFamily_elementary H hΩ
  let Sg := (S : Subgroup H).map H.subtype
  have hSM : Sg ≤ M := (Sg.le_normalizer.trans (normalizer_le_weakClosure_normalizer V Sg 0)).trans hNM
  have hSMH : (S : Subgroup H) ≤ M.subgroupOf H := map_le_iff_le_comap.mp hSM
  have hWmap : (weakClosure (S : Subgroup H) ΩH).map H.subtype = indexedWeakClosure V Sg 0 := by
    have he := ChiefOrbit.map_weakClosure_restrictedFamily Sg H (map_subtype_le _) Ω
    have hsub : Sg.subgroupOf H = (S : Subgroup H) := by
      change ((S : Subgroup H).map H.subtype).comap H.subtype = (S : Subgroup H)
      rw [comap_map_eq_self_of_injective H.subtype_injective]
    rwa [hsub] at he
  have hN : normalizer (weakClosure (S : Subgroup H) ΩH : Set H) ≤ M.subgroupOf H := by
    apply map_le_iff_le_comap.mp
    apply le_trans (Subgroup.le_normalizer_map H.subtype)
    rw [hWmap]
    exact hNM
  have hE : eFamilySubgroup 1 (S : Subgroup H) ΩH ≤ M.subgroupOf H := by
    apply iSup_le
    intro A
    apply sSup_le
    intro K hK
    have hA := A.property.1
    have hAS : A.val.map H.subtype ≤ Sg := map_mono A.property.2
    obtain ⟨g, hAg, _⟩ := (mem_gamma_zero_iff V Sg (A.val.map H.subtype)).mp ⟨hA, hAS⟩
    let AK := A.val.subgroupOf K
    let _ : IsElementaryAbelian 2 A.val := hK.1.1
    let _ : IsElementaryAbelian 2 AK := IsElementaryAbelian.subgroupOf hK.1.2.2.1
    let f := H.subtype.comp K.subtype
    have hf : Function.Injective f := H.subtype_injective.comp K.subtype_injective
    have heA : AK.map f = V.map (MulAut.conj g).toMonoidHom := by
      rw [← map_map, map_subgroupOf_eq_of_le hK.1.2.2.1]
      exact hAg
    have hcore : (pCore 2 K).map f ≤ Sg := by
      obtain ⟨U, hU⟩ := hK.1.2.2.2.2.1
      have hcu := map_mono (f := K.subtype) (pCore_isPGroup.le_sylow_of_normal U)
      rw [hU, subgroupOf_map_subtype] at hcu
      change (pCore 2 K).map (H.subtype.comp K.subtype) ≤ Sg
      rw [← map_map]
      exact map_mono (hcu.trans inf_le_left)
    have hcorank : subgroupCorank AK (AK ⊓ pCore 2 K) = 1 := by
      have hle := SourceContainment.core_corank_le AK
        (ValuesEvenClassical.Sp4Lower.member_core_rank_le hK)
      have hne : subgroupCorank AK (AK ⊓ pCore 2 K) ≠ 0 := by
        intro he
        have hEq := subgroup_eq_of_corank_zero (inf_le_left : AK ⊓ pCore 2 K ≤ AK) he
        exact ValuesEvenClassical.Sp4Lower.member_not_le_core hK.1
          (hEq.symm.le.trans inf_le_right)
      omega
    have hNC := normalClosure_centralizes_one (S.isPGroup'.map H.subtype)
      AK f hf g heA hcore hcorank hs
    have hRC : (pResidual 2 K).map f ≤ centralizer (weakCentralizer V Sg 1 : Set G) :=
      (map_mono hK.1.residual_le_normalClosure).trans hNC
    apply hK.1.le_of_residual_le hSMH
    rintro x ⟨k, hk, rfl⟩
    exact hCV ⟨k.val.property, hRC (mem_map_of_mem f hk)⟩
  have htop : (⊤ : Subgroup H) ≤ M.subgroupOf H := by
    rw [← hgen ΩH hΩH]
    exact sup_le hE hN
  intro x hx
  exact htop (show (⟨x, hx⟩ : H) ∈ (⊤ : Subgroup H) from mem_top _)


end CFSG.Quasithin.ChapterE.WeakCentralizerContainment
