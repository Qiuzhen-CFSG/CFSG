module
public import CFSG.Quasithin.ChapterE.Section03.SourceContainment

/-!
# Containment from centralizing weak closures in the actual local Sylow

Suppose W_j(S,V) centralizes V for j ≤ i < s(G,V). For each E_i-member,
every conjugate of its elementary generator meets its two-core in corank
at most i. That intersection lies in S, hence centralizes V. E.3.7 makes
the whole conjugate centralize V. Its normal closure contains the member's
two-residual, so E-generation and control of N_G(W₀(S,V)) put the overgroup
in M.

This form of the E.3.19 argument retains the actual relative Sylow subgroup
and a proved E-generation witness. The tensor consumer discharges the local
weak-closure premises and uses positive attainment when n(H)=1 or 2; the
solvable case uses the unconditional E.1.13 witness.
Source: Aschbacher--Smith E.1.4, E.3.7 and E.3.19, printed pp.210,231--234;
applications 8.3.6 and the end of 8.3.1, printed pp.724,727.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.LocalContainment
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

private theorem normalClosure_centralizes {V S : Subgroup G} [IsElementaryAbelian 2 V]
    (hSN : S ≤ normalizer (V : Set G))
    {K : Type*} [Group K] [Finite K] (A : Subgroup K) [IsElementaryAbelian 2 A]
    (f : K →* G) (hf : Function.Injective f) (g : G)
    (hAg : A.map f = V.map (MulAut.conj g).toMonoidHom)
    (hcore : (pCore 2 K).map f ≤ S) {i : ℕ}
    (hrank : Group.rank (A.map (QuotientGroup.mk' (pCore 2 K))) ≤ i)
    (hW : ∀ j ≤ i, indexedWeakClosure V S j ≤ centralizer (V : Set G))
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
    have hBC : ((A ⊓ pCore 2 K).map f') ≤ S := by
      apply le_trans _ hcore
      rintro x ⟨a, ha, rfl⟩
      exact mem_map_of_mem f ((inferInstance : (pCore 2 K).Normal).conj_mem a ha.2 k)
    have hb : subgroupCorank (V.map (MulAut.conj (f k * g)).toMonoidHom)
        ((A ⊓ pCore 2 K).map f') ≤ i := by
      rw [← he, subgroupCorank, relIndex_map_map_of_injective _ _ hinj]
      exact hi
    rw [he]
    exact conjugate_centralizes hSN hW hs (f k * g)
      (he ▸ map_mono inf_le_left) hBC hb
  apply map_le_iff_le_comap.mpr
  change Subgroup.closure (Group.conjugatesOfSet (A : Set K)) ≤ _
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨k, rfl⟩ := isConj_iff.mp hax
  exact hconj k (mem_map_of_mem _ ha)


/-- Local weak closures below s and their zeroth normalizer control an E-generated overgroup. -/
theorem le_of_isEGenerated {V M H : Subgroup G} [IsElementaryAbelian 2 V]
    (S : Sylow 2 H) {i : ℕ} (hgen : IsEGeneratedAt i S)
    (hSN : (S : Subgroup H).map H.subtype ≤ normalizer (V : Set G))
    (hNM : normalizer (indexedWeakClosure V ((S : Subgroup H).map H.subtype) 0 : Set G) ≤ M)
    (hCV : H ⊓ centralizer (V : Set G) ≤ M)
    (hW : ∀ j ≤ i, indexedWeakClosure V ((S : Subgroup H).map H.subtype) j ≤
      centralizer (V : Set G)) (hs : (i : ℕ∞) < globalS V) : H ≤ M := by
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
  have hE : eFamilySubgroup i (S : Subgroup H) ΩH ≤ M.subgroupOf H := by
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
    have hNC := normalClosure_centralizes hSN AK f hf g heA hcore
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


end CFSG.Quasithin.ChapterE.LocalContainment
