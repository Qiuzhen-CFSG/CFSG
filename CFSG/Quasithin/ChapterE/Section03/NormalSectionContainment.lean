module
public import CFSG.Quasithin.ChapterE.Section03.LocalContainment
/-!
# E-generation inside a normalized section

Restrict the conjugate family of V to a subgroup Y normalized by the
E-generated overgroup H. Its weak closure in a Sylow subgroup T of H is
then the original weak closure in T intersect Y. Every conjugate of an
E-member's elementary generator stays in Y, so its intersection with the
member's two-core lies in T intersect Y. The small-corank centralization
argument and normalizer control force H into M.

This is a normal-section form of E.3.19, retaining the literal weak closures
and the full ambient conjugate family. The application to 8.3.7 treats
parameter-one Suzuki H-stars without equating generation parameters across
a two-core quotient.
Source: Aschbacher--Smith E.1.4, E.3.7, E.3.19 and 8.3.7,
printed pp.210,231--234,724--725.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.NormalSectionContainment
variable {G : Type*} [Group G] [Finite G]

private theorem conjugate_centralizes {V S B : Subgroup G} [IsElementaryAbelian 2 V]
    (hSN : S ≤ normalizer (V : Set G)) {i : ℕ}
    (hW : ∀ j ≤ i, indexedWeakClosure V S j ≤ centralizer (V : Set G))
    (hs : (i : ℕ∞) < globalS V) (g : G)
    (hBV : B ≤ V.map (MulAut.conj g).toMonoidHom) (hBS : B ≤ S)
    (hi : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B ≤ i) :
    V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hgamma : B ∈ gamma V S (subgroupCorank W B) := by
    refine ⟨⟨g,hBV,?_⟩,hBS⟩
    rw [Subgroup.relIndex_eq_two_pow_quotient_finrank,subgroupCorank_eq_quotient_finrank]
  have hBC : B ≤ centralizer (V : Set G) := (gamma_le_weakClosure hgamma).trans (hW _ hi)
  have hc := lemma_E_3_7 g (le_inf hBV (hBS.trans hSN))
    (lt_of_le_of_lt (by exact_mod_cast hi) hs)
  apply le_centralizer_iff.mpr
  have hh : V ≤ V ⊓ centralizer (B : Set G) := le_inf le_rfl (le_centralizer_iff.mp hBC)
  exact (hh.trans_eq hc).trans inf_le_right

private theorem normalClosure_centralizes {V S Y : Subgroup G} [IsElementaryAbelian 2 V]
    (hSN : S ≤ normalizer (V : Set G))
    {K : Type*} [Group K] [Finite K] (A : Subgroup K) [IsElementaryAbelian 2 A]
    (f : K →* G) (hf : Function.Injective f) (g : G)
    (hAg : A.map f = V.map (MulAut.conj g).toMonoidHom)
    (hcore : (pCore 2 K).map f ≤ S)
    (hAY : A.map f ≤ Y) (hNY : f.range ≤ normalizer (Y : Set G)) {i : ℕ}
    (hrank : Group.rank (A.map (QuotientGroup.mk' (pCore 2 K))) ≤ i)
    (hW : ∀ j ≤ i, indexedWeakClosure V (S ⊓ Y) j ≤ centralizer (V : Set G))
    (hs : (i : ℕ∞) < globalS V) :
    (normalClosure (A : Set K)).map f ≤ centralizer (V : Set G) := by
  have hi := SourceContainment.core_corank_le A hrank
  have hconj (k : K) :
      (A.map (f.comp (MulAut.conj k).toMonoidHom)) ≤ centralizer (V : Set G) := by
    let f' := f.comp (MulAut.conj k).toMonoidHom
    have hinj : Function.Injective f' := hf.comp (MulAut.conj k).injective
    have he : A.map f' = V.map (MulAut.conj (f k * g)).toMonoidHom := by
      have hcomp : f' = (MulAut.conj (f k)).toMonoidHom.comp f := by ext x; simp [f']
      rw [hcomp, ← map_map, hAg, map_map]
      congr 1
      ext x
      simp [mul_assoc]
    have hBC : ((A ⊓ pCore 2 K).map f') ≤ S ⊓ Y := by
      rintro x ⟨a, ha, rfl⟩
      refine ⟨hcore (mem_map_of_mem f
        ((inferInstance : (pCore 2 K).Normal).conj_mem a ha.2 k)), ?_⟩
      have hn := hNY (show f k ∈ f.range from ⟨k,rfl⟩)
      have hay := hAY (mem_map_of_mem f ha.1)
      change f' a ∈ Y
      simpa only [f', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv] using
        (Subgroup.mem_normalizer_iff.mp hn (f a)).mp hay
    have hb : subgroupCorank (V.map (MulAut.conj (f k * g)).toMonoidHom)
        ((A ⊓ pCore 2 K).map f') ≤ i := by
      rw [← he, subgroupCorank, relIndex_map_map_of_injective _ _ hinj]
      exact hi
    rw [he]
    exact conjugate_centralizes (inf_le_left.trans hSN) hW hs (f k * g)
      (he ▸ map_mono inf_le_left) hBC hb
  apply map_le_iff_le_comap.mpr
  change Subgroup.closure (Group.conjugatesOfSet (A : Set K)) ≤ _
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨k, rfl⟩ := isConj_iff.mp hax
  exact hconj k (mem_map_of_mem _ ha)



/-- E-generation inside a normal section uses weak closures in its Sylow intersection. -/
theorem le_of_isEGenerated {V M H Y : Subgroup G} [IsElementaryAbelian 2 V]
    (S : Sylow 2 H) {i : ℕ} (hgen : IsEGeneratedAt i S)
    (hHY : H ≤ normalizer (Y : Set G))
    (hSN : (S : Subgroup H).map H.subtype ≤ normalizer (V : Set G))
    (hNM : normalizer (indexedWeakClosure V
      ((S : Subgroup H).map H.subtype ⊓ Y) 0 : Set G) ≤ M)
    (hCV : H ⊓ centralizer (V : Set G) ≤ M)
    (hW : ∀ j ≤ i, indexedWeakClosure V ((S : Subgroup H).map H.subtype ⊓ Y) j ≤
      centralizer (V : Set G)) (hs : (i : ℕ∞) < globalS V) : H ≤ M := by
  let Ω := conjugateCorankFamily V 0
  have hΩ : IsElementaryFamily Ω := by
    constructor
    · rintro A ⟨g, hAV, hi⟩
      let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
      exact IsElementaryAbelian.of_injective (Subgroup.inclusion hAV) (Subgroup.inclusion_injective _)
    · intro g A hA
      exact conjugateCorankFamily_invariant V 0 A hA g
  let Ψ : Set (Subgroup G) := {A | A ∈ Ω ∧ A ≤ Y}
  let ΩH := ChiefOrbit.restrictedFamily H Ψ
  have hΩH : IsElementaryFamily ΩH := by
    constructor
    · intro A hA
      exact (ChiefOrbit.restrictedFamily_elementary H hΩ).1 A hA.1
    · intro g A hA
      have he : (A.map (MulAut.conj g).toMonoidHom).map H.subtype =
          (A.map H.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
        rw [map_map,map_map]; rfl
      change (A.map (MulAut.conj g).toMonoidHom).map H.subtype ∈ Ψ
      rw [he]
      refine ⟨hΩ.2 g _ hA.1,?_⟩
      exact (map_mono hA.2).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hHY g.property))
  let Sg := (S : Subgroup H).map H.subtype
  have hSM : Sg ≤ M := by
    apply le_trans ?_ hNM
    apply le_trans ?_ (normalizer_le_weakClosure_normalizer V (Sg ⊓ Y) 0)
    exact (le_inf Sg.le_normalizer ((map_subtype_le _).trans hHY)).trans
      inf_normalizer_le_normalizer_inf
  have hSMH : (S : Subgroup H) ≤ M.subgroupOf H := map_le_iff_le_comap.mp hSM
  have hWmap : (weakClosure (S : Subgroup H) ΩH).map H.subtype =
      indexedWeakClosure V (Sg ⊓ Y) 0 := by
    have he := ChiefOrbit.map_weakClosure_restrictedFamily Sg H (map_subtype_le _) Ψ
    have hsub : Sg.subgroupOf H = (S : Subgroup H) := by
      change ((S : Subgroup H).map H.subtype).comap H.subtype = (S : Subgroup H)
      rw [comap_map_eq_self_of_injective H.subtype_injective]
    rw [hsub] at he
    rw [he]
    change sSup {A | (A ∈ Ω ∧ A ≤ Y) ∧ A ≤ Sg} = sSup {A | A ∈ Ω ∧ A ≤ Sg ⊓ Y}
    congr 1
    ext A
    simp only [Set.mem_ofPred_eq,le_inf_iff]
    tauto
  have hN : normalizer (weakClosure (S : Subgroup H) ΩH : Set H) ≤ M.subgroupOf H := by
    apply map_le_iff_le_comap.mp
    apply le_trans (Subgroup.le_normalizer_map H.subtype)
    rw [hWmap]
    exact hNM
  have hE : eFamilySubgroup i (S : Subgroup H) ΩH ≤ M.subgroupOf H := by
    apply iSup_le
    intro A
    apply sSup_le
    intro K hK
    have hA := A.property.1
    have hAS : A.val.map H.subtype ≤ Sg := map_mono A.property.2
    obtain ⟨g, hAg, _⟩ := (mem_gamma_zero_iff V Sg (A.val.map H.subtype)).mp ⟨hA.1, hAS⟩
    let AK := A.val.subgroupOf K
    let _ : IsElementaryAbelian 2 A.val := hK.1.1
    let _ : IsElementaryAbelian 2 AK := IsElementaryAbelian.subgroupOf hK.1.2.2.1
    let f := H.subtype.comp K.subtype
    have hf : Function.Injective f := H.subtype_injective.comp K.subtype_injective
    have heA : AK.map f = V.map (MulAut.conj g).toMonoidHom := by
      rw [← map_map, map_subgroupOf_eq_of_le hK.1.2.2.1]
      exact hAg
    have hAY : AK.map f ≤ Y := by
      rw [← map_map, map_subgroupOf_eq_of_le hK.1.2.2.1]
      exact hA.2
    have hNY : f.range ≤ normalizer (Y : Set G) := by
      rintro x ⟨k,rfl⟩
      exact hHY k.val.property
    have hcore : (pCore 2 K).map f ≤ Sg := by
      obtain ⟨U, hU⟩ := hK.1.2.2.2.2.1
      have hcu := map_mono (f := K.subtype) (pCore_isPGroup.le_sylow_of_normal U)
      rw [hU, subgroupOf_map_subtype] at hcu
      change (pCore 2 K).map (H.subtype.comp K.subtype) ≤ Sg
      rw [← map_map]
      exact map_mono (hcu.trans inf_le_left)
    have hNC := normalClosure_centralizes hSN AK f hf g heA hcore hAY hNY
      (ValuesEvenClassical.Sp4Lower.member_core_rank_le hK) hW hs
    have hRC : (pResidual 2 K).map f ≤ centralizer (V : Set G) :=
      (map_mono hK.1.residual_le_normalClosure).trans hNC
    apply hK.1.le_of_residual_le hSMH
    rintro x ⟨k, hk, rfl⟩
    exact hCV ⟨k.val.property, hRC (mem_map_of_mem f hk)⟩
  have htop : (⊤ : Subgroup H) ≤ M.subgroupOf H := by
    rw [← hgen ΩH hΩH]
    exact sup_le hE hN
  intro x hx
  exact htop (show (⟨x, hx⟩ : H) ∈ (⊤ : Subgroup H) from mem_top _)

end CFSG.Quasithin.ChapterE.NormalSectionContainment
