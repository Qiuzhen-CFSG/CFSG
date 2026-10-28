module

public import CFSG.Quasithin.ChapterE.Section03.SourceContainment
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Rigidity

/-!
# Rank-one relative-Sylow generation below s

This is E.3.19 for i = 0 and j = 1. For an E-member K and its elementary
subgroup A, the actual quotient rank is at most one and A is not contained
in O₂(K). Hence A intersects O₂(K) in corank exactly one. Every K-conjugate
of that intersection is a generator of W₁(R), where R is the ambient image
of the specified Sylow subgroup of H. Centralizer rigidity E.3.6, applied
to the two-group C₁(R), makes C₁(R) centralize every K-conjugate of A.
E.1.4 then puts O²(K) in C_G(C₁(R)). This proves the residual-centralization
step needed from E.3.17--19 without the other clauses of E.3.17.

E-generation and the Sylow supplement now give the literal ambient join
identity. The positive value n(H) = 1 supplies attainment. Only the corank
bound is reused from SourceContainment; its different E.3.35 containment
hypotheses are not used.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
E.3.17--19, printed pp.233--235; application in 11.5.1, pp.778--779.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.RankOneWeakClosure
variable {G : Type*} [Group G] [Finite G]

private theorem core_corank_eq_one {K : Type*} [Group K] [Finite K]
    (A : Subgroup K) [IsElementaryAbelian 2 A]
    (hr : Group.rank (A.map (QuotientGroup.mk' (pCore 2 K))) ≤ 1)
    (hn : ¬ A ≤ pCore 2 K) : subgroupCorank A (A ⊓ pCore 2 K) = 1 := by
  have hle := SourceContainment.core_corank_le A hr
  have hpos : subgroupCorank A (A ⊓ pCore 2 K) ≠ 0 := by
    intro hz
    have hi : (A ⊓ pCore 2 K).relIndex A = 1 := by
      rw [Subgroup.relIndex_eq_two_pow_quotient_finrank,
        ← subgroupCorank_eq_quotient_finrank, hz, pow_zero]
    exact hn ((Subgroup.relIndex_eq_one.mp hi).trans inf_le_right)
  omega

private theorem normalClosure_centralizes {V R : Subgroup G} [IsElementaryAbelian 2 V]
    (hR : IsPGroup 2 R) (hs : (1 : ℕ∞) < globalS V)
    {K : Type*} [Group K] [Finite K] (A : Subgroup K) [IsElementaryAbelian 2 A]
    (f : K →* G) (hf : Function.Injective f) (g : G)
    (hAg : A.map f = V.map (MulAut.conj g).toMonoidHom)
    (hcore : (pCore 2 K).map f ≤ R)
    (hr : Group.rank (A.map (QuotientGroup.mk' (pCore 2 K))) ≤ 1)
    (hn : ¬ A ≤ pCore 2 K) :
    (normalClosure (A : Set K)).map f ≤ centralizer (weakCentralizer V R 1 : Set G) := by
  have hi := core_corank_eq_one A hr hn
  have hconj (k : K) :
      A.map (f.comp (MulAut.conj k).toMonoidHom) ≤
        centralizer (weakCentralizer V R 1 : Set G) := by
    let f' := f.comp (MulAut.conj k).toMonoidHom
    have hinj : Function.Injective f' := hf.comp (MulAut.conj k).injective
    have he : A.map f' = V.map (MulAut.conj (f k * g)).toMonoidHom := by
      have hcomp : f' = (MulAut.conj (f k)).toMonoidHom.comp f := by ext x; simp [f']
      rw [hcomp, ← map_map, hAg, map_map]
      congr 1
      ext x
      simp [mul_assoc]
    let B := (A ⊓ pCore 2 K).map f'
    let W := V.map (MulAut.conj (f k * g)).toMonoidHom
    let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
    have hBW : B ≤ W := by
      change B ≤ V.map (MulAut.conj (f k * g)).toMonoidHom
      rw [← he]
      exact map_mono inf_le_left
    have hBR : B ≤ R := by
      apply le_trans _ hcore
      rintro x ⟨a, ha, rfl⟩
      exact mem_map_of_mem f ((inferInstance : (pCore 2 K).Normal).conj_mem a ha.2 k)
    have hb : subgroupCorank W B = 1 := by
      change subgroupCorank (V.map (MulAut.conj (f k * g)).toMonoidHom) B = 1
      rw [← he]
      change Nat.log 2 (((A ⊓ pCore 2 K).map f').relIndex (A.map f')) = 1
      rw [relIndex_map_map_of_injective _ _ hinj]
      exact hi
    have hgamma : B ∈ gamma V R 1 := by
      refine ⟨⟨f k * g, hBW, ?_⟩, hBR⟩
      change B.relIndex W = 2 ^ 1
      rw [Subgroup.relIndex_eq_two_pow_quotient_finrank,
        ← subgroupCorank_eq_quotient_finrank, hb]
    have hCB : weakCentralizer V R 1 ≤ centralizer (B : Set G) :=
      inf_le_right.trans (centralizer_le (gamma_le_weakClosure hgamma))
    have hbs : (subgroupCorank W B : ℕ∞) < globalS W := by
      rw [hb, show globalS W = globalS V from globalS_map_equiv _ _]
      exact hs
    have hc := centralizer_inf_eq_of_corank_lt_globalS
      (E := weakCentralizer V R 1) hBW hbs hR.to_inf_left
    apply le_centralizer_iff.mpr
    rw [he]
    exact (le_inf le_rfl hCB).trans (hc.le.trans inf_le_right)
  apply map_le_iff_le_comap.mpr
  change Subgroup.closure (Group.conjugatesOfSet (A : Set K)) ≤ _
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨k, rfl⟩ := isConj_iff.mp hax
  exact hconj k (mem_map_of_mem _ ha)

/-- The E.3.17--19 residual step for the actual rank-one E-member, with its
inclusion in the ambient group and its Sylow image kept explicit. -/
theorem member_residual_centralizes {V R : Subgroup G} [IsElementaryAbelian 2 V]
    (hR : IsPGroup 2 R) (hs : (1 : ℕ∞) < globalS V)
    {H : Type*} [Group H] [Finite H] {T A K : Subgroup H}
    (hK : IsEMemberAt 1 T A K) (f : H →* G) (hf : Function.Injective f)
    (g : G) (hAg : A.map f = V.map (MulAut.conj g).toMonoidHom)
    (hTR : T.map f ≤ R) :
    (pResidual 2 K).map (f.comp K.subtype) ≤
      centralizer (weakCentralizer V R 1 : Set G) := by
  let AK := A.subgroupOf K
  let _ : IsElementaryAbelian 2 A := hK.1.1
  let _ : IsElementaryAbelian 2 AK := IsElementaryAbelian.subgroupOf hK.1.2.2.1
  have heA : AK.map (f.comp K.subtype) = V.map (MulAut.conj g).toMonoidHom := by
    rw [← map_map, map_subgroupOf_eq_of_le hK.1.2.2.1]
    exact hAg
  have hcore : (pCore 2 K).map (f.comp K.subtype) ≤ R := by
    obtain ⟨U, hU⟩ := hK.1.2.2.2.2.1
    have hcu := map_mono (f := K.subtype) (pCore_isPGroup.le_sylow_of_normal U)
    rw [hU, subgroupOf_map_subtype] at hcu
    rw [← map_map]
    exact (map_mono (hcu.trans inf_le_left)).trans hTR
  exact (map_mono hK.1.residual_le_normalClosure).trans
    (normalClosure_centralizes hR hs AK (f.comp K.subtype)
      (hf.comp K.subtype_injective) g heA hcore
      (ValuesEvenClassical.Sp4Lower.member_core_rank_le hK)
      (ValuesEvenClassical.Sp4Lower.member_not_le_core hK.1))

/-- E.3.19 for an attained rank-one generation bound at the specified relative Sylow. -/
theorem generation_of_isEGenerated {V H : Subgroup G} [IsElementaryAbelian 2 V]
    (S : Sylow 2 H) (hgen : IsEGeneratedAt 1 S)
    (hs : (1 : ℕ∞) < globalS V) :
    H = (H ⊓ centralizer (weakCentralizer V ((S : Subgroup H).map H.subtype) 1 : Set G)) ⊔
      (H ⊓ normalizer (indexedWeakClosure V ((S : Subgroup H).map H.subtype) 0 : Set G)) := by
  let R := (S : Subgroup H).map H.subtype
  let C := weakCentralizer V R 1
  let N := normalizer (indexedWeakClosure V R 0 : Set G)
  let M := (H ⊓ centralizer (C : Set G)) ⊔ (H ⊓ N)
  have hRM : R ≤ M := le_sup_of_le_right (le_inf (map_subtype_le _)
    (R.le_normalizer.trans (normalizer_le_weakClosure_normalizer V R 0)))
  let Ω := conjugateCorankFamily V 0
  have hΩ : IsElementaryFamily Ω := by
    constructor
    · rintro A ⟨g, hAV, _⟩
      let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
        IsElementaryAbelian.map _
      exact IsElementaryAbelian.of_injective (Subgroup.inclusion hAV)
        (Subgroup.inclusion_injective _)
    · intro g A hA
      exact conjugateCorankFamily_invariant V 0 A hA g
  let ΩH := ChiefOrbit.restrictedFamily H Ω
  have hΩH : IsElementaryFamily ΩH := ChiefOrbit.restrictedFamily_elementary H hΩ
  have hWmap : (weakClosure (S : Subgroup H) ΩH).map H.subtype = indexedWeakClosure V R 0 := by
    have he := ChiefOrbit.map_weakClosure_restrictedFamily R H (map_subtype_le _) Ω
    have hsub : R.subgroupOf H = (S : Subgroup H) := by
      change ((S : Subgroup H).map H.subtype).comap H.subtype = (S : Subgroup H)
      rw [comap_map_eq_self_of_injective H.subtype_injective]
    rwa [hsub] at he
  have hN : normalizer (weakClosure (S : Subgroup H) ΩH : Set H) ≤ M.subgroupOf H := by
    apply map_le_iff_le_comap.mp
    apply le_sup_of_le_right
    apply le_inf (map_subtype_le _)
    apply le_trans (Subgroup.le_normalizer_map H.subtype)
    rw [hWmap]
  have hE : eFamilySubgroup 1 (S : Subgroup H) ΩH ≤ M.subgroupOf H := by
    apply iSup_le
    intro A
    apply sSup_le
    intro K hK
    have hAS : A.val.map H.subtype ≤ R := map_mono A.property.2
    obtain ⟨g, hAg, _⟩ := (mem_gamma_zero_iff V R (A.val.map H.subtype)).mp
      ⟨A.property.1, hAS⟩
    have hRC := member_residual_centralizes (S.2.map H.subtype) hs hK
      H.subtype H.subtype_injective g hAg le_rfl
    apply hK.1.le_of_residual_le (map_le_iff_le_comap.mp hRM)
    rintro x ⟨k, hk, rfl⟩
    exact (le_sup_left : H ⊓ centralizer (C : Set G) ≤ M)
      ⟨k.val.property, hRC (mem_map_of_mem (H.subtype.comp K.subtype) hk)⟩
  have htop : (⊤ : Subgroup H) ≤ M.subgroupOf H := by
    rw [← hgen ΩH hΩH]
    exact sup_le hE hN
  apply le_antisymm
  · intro x hx
    exact htop (show (⟨x, hx⟩ : H) ∈ (⊤ : Subgroup H) from mem_top _)
  · exact sup_le inf_le_left inf_le_left

/-- The literal ambient E.3.19 identity for n(H) = 1 and 1 < s(G,V). -/
theorem generation_of_parameter_eq_one {V H : Subgroup G} [IsElementaryAbelian 2 V]
    (S : Sylow 2 H) (hn : generationParameter H = 1)
    (hs : (1 : ℕ∞) < globalS V) :
    H = (H ⊓ centralizer (weakCentralizer V ((S : Subgroup H).map H.subtype) 1 : Set G)) ⊔
      (H ⊓ normalizer (indexedWeakClosure V ((S : Subgroup H).map H.subtype) 0 : Set G)) := by
  have hg := isEGenerated_generationParameter_of_pos (G := H) (by omega)
  rw [hn] at hg
  exact generation_of_isEGenerated S (hg S) hs

/-- The two ambient bounds in 11.5.1 force the rank-one overgroup into M. -/
theorem le_of_parameter_eq_one {V H M : Subgroup G} [IsElementaryAbelian 2 V]
    (S : Sylow 2 H) (hn : generationParameter H = 1)
    (hs : (1 : ℕ∞) < globalS V)
    (hC : centralizer (weakCentralizer V ((S : Subgroup H).map H.subtype) 1 : Set G) ≤ M)
    (hN : normalizer (indexedWeakClosure V ((S : Subgroup H).map H.subtype) 0 : Set G) ≤ M) :
    H ≤ M := by
  rw [generation_of_parameter_eq_one S hn hs]
  exact sup_le (inf_le_right.trans hC) (inf_le_right.trans hN)

end CFSG.Quasithin.ChapterE.RankOneWeakClosure
