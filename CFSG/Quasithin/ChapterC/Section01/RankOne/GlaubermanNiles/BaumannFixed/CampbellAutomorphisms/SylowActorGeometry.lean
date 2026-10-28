module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.ActorSupplement
public import Theory.GroupTheory.AutomorphismMaximumElementary
/-!
# The actual transported natural actor supplements the two-core

For α∈Aut(S), W=⟨(F^α)^J(H)⟩ and W′=W^(α⁻¹), let b be the literal
restricted α-equivalence. The inverse image X of V under b⁻¹c_u b is an
actual subgroup of S. The transport maps X onto V and fixes Z=C_V(S),
because b(Z)=Z^α is central in J(H). A maximum elementary replacement
containing F^α in O₂(H), conjugated and transported back, contains X.
Thus the checked core-intersection and index theorem applies: if X moves
F, then XO₂(H)=S. Every transport, fixedness and replacement premise is
constructed from the original local class and the source noncontainments.
Source: Campbell II.6.3, printed pp.30–31, for the Aut(S) corollary.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H]

@[expose] noncomputable def spanNaturalActor (W W' : Subgroup H) (b : W' ≃* W)
    (u : normalizer (W : Set H)) : Subgroup H :=
  ((Campbell.V H).comap (spanConjugationMap W W' b u)).map W'.subtype

omit [Finite H] in
private theorem span_map_range (W W' : Subgroup H) (b : W' ≃* W)
    (u : normalizer (W : Set H)) : (spanConjugationMap W W' b u).range=W' := by
  unfold spanConjugationMap
  rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr
    (((b.trans (W.normalizerMonoidHom u)).trans b.symm).surjective),
    ←MonoidHom.range_eq_map,range_subtype]

variable (S : Subgroup H)
theorem InLocalClass.sylow_actor_sup_core (h : InLocalClass S.subtype) (hB : IsBaumannFixed S)
    (a : MulAut S) (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H)
    (hF : ¬ automorphismImage S a (Campbell.F H) ≤ Campbell.F H) :
    let W := conjugateSpanBy (automorphismImage S a (Campbell.F H)) (Campbell.J (⊤ : Subgroup H))
    let W' := automorphismImage S a.symm W
    ∀ b : W' ≃* W,
      (∀ w : W', (b w : H) = (a ⟨w,automorphismImage_le S a.symm W w.property⟩ : H)) →
      ∀ u : normalizer (W : Set H), (u:H) ∈ Campbell.J (⊤ : Subgroup H) →
        ¬ Campbell.F H ≤ centralizer (spanNaturalActor W W' b u : Set H) →
          spanNaturalActor W W' b u ⊔ pCore 2 H=S := by
  let Y := automorphismImage S a (Campbell.F H)
  let K := Campbell.J (⊤ : Subgroup H)
  let W := conjugateSpanBy Y K
  let W' := automorphismImage S a.symm W
  dsimp only
  intro b hb u hu hmove
  let f := spanConjugationMap W W' b u
  let γ := (b.trans (W.normalizerMonoidHom u)).trans b.symm
  let X := spanNaturalActor W W' b u
  let Z := Campbell.V H ⊓ centralizer (S:Set H)
  have hs := h.sylow_automorphism_span S hB a hV
  have hFr : Campbell.F H ≤ W' := hs.2.2.2.2.2
  have hVr : Campbell.V H ≤ W' := Campbell.V_le_F.trans hFr
  have hXr : X ≤ W' := (map_le_range _ _).trans (by rw [range_subtype])
  have hWrS : W' ≤ S := automorphismImage_le S a.symm W
  have hfr : f.range=W' := span_map_range W W' b u
  have hf : Function.Injective f := W'.subtype_injective.comp γ.injective
  have hfX : (X.subgroupOf W').map f = Campbell.V H := by
    change ((((Campbell.V H).comap f).map W'.subtype).comap W'.subtype).map f = _
    rw [comap_map_eq_self_of_injective W'.subtype_injective,map_comap_eq]
    exact inf_eq_right.mpr (by rwa [hfr])
  have hZa := h.sylow_automorphism_fixed_central S hB a hV hF
  have hfZ : ∀ z : W', (z:H) ∈ Z → f z=(z:H) := by
    intro z hz
    have hbz : (b z:H) ∈ automorphismImage S a Z := by
      rw [hb z]
      exact mem_map_of_mem S.subtype (mem_map_of_mem a.toMonoidHom hz)
    have huz : W.normalizerMonoidHom u (b z)=b z := by
      apply Subtype.ext
      change (u:H)*(b z:H)*(u:H)⁻¹=(b z:H)
      have hcomm : (u:H)*(b z:H)=(b z:H)*(u:H) := hZa hbz u hu
      rw [hcomm,mul_inv_cancel_right]
    change (b.symm (W.normalizerMonoidHom u (b z)) : H)=(z:H)
    rw [huz,b.symm_apply_apply]
  have hZX : Z ≤ X := by
    intro z hz
    let z' : W' := ⟨z,hVr hz.1⟩
    refine ⟨z',?_,rfl⟩
    change f z' ∈ Campbell.V H
    rw [hfZ z' hz]
    exact hz.1
  obtain ⟨d,_,hSd⟩ := h.exists_campbellEmbedding hB
  have hSd' : (d.sylow:Subgroup H)=S := hSd.trans (range_subtype S)
  obtain ⟨A,hA,hFA⟩ := h.campbellF_le_some_maxElementary hB d
  rw [hSd'] at hA
  let B0 := automorphismImage S a A
  have hB0 : B0 ∈ elementaryAbelianMaxSubgroups S := automorphismImage_maxElementary S a A hA
  let E0 := (B0 ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H)
  have hE0 := h.omegaCore_replacement_maximal hB d B0 (by rw [hSd']; exact hB0)
  have hE0Q : E0 ≤ pCore 2 H := sup_le inf_le_right
    (fun z hz => ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1)
  have hYE0 : Y ≤ E0 := (le_inf (automorphismImage_mono S a hFA)
    ((le_conjugateSpanBy Y K).trans hs.1)).trans le_sup_left
  let E := E0.map (MulAut.conj (u:H)⁻¹).toMonoidHom
  have hE : E ∈ elementaryAbelianMaxSubgroups S := by
    have hh := maxElementary_conjugate_of_le_core d.sylow (u:H)⁻¹ E0 hE0 hE0Q
    rwa [hSd'] at hh
  let A1 := automorphismImage S a.symm E
  have hA1 : A1 ∈ elementaryAbelianMaxSubgroups S := automorphismImage_maxElementary S a.symm E hE
  have hXA1 : X ≤ A1 := by
    rintro z ⟨w,hw,rfl⟩
    let v := γ w
    have hv : (v:H) ∈ Campbell.V H := hw
    have hbv : (b v:H) ∈ Y := by
      rw [hb v]
      exact mem_map_of_mem S.subtype (mem_map_of_mem a.toMonoidHom (Campbell.V_le_F hv))
    have hbe : (b w:H) ∈ E := by
      have hword : b w=(W.normalizerMonoidHom u).symm (b v) := by
        dsimp [v,γ]
        simp
      rw [hword]
      exact mem_map_of_mem (MulAut.conj (u:H)⁻¹).toMonoidHom (hYE0 hbv)
    rw [hb w] at hbe
    have hbeS : (a ⟨w,hWrS w.property⟩ : S) ∈ E.subgroupOf S := hbe
    have hh := mem_map_of_mem S.subtype (mem_map_of_mem a.symm.toMonoidHom hbeS)
    change (a.symm (a ⟨w,hWrS w.property⟩):H) ∈ A1 at hh
    change (w:H) ∈ A1
    simpa only [a.symm_apply_apply] using hh
  have hout := h.transported_actor_sup_core_eq_sylow hB W' X A1 f hf hFr hXr
    (by simpa only [range_subtype] using hXr.trans hWrS)
    (by simpa only [range_subtype,hfr] using hWrS)
    (by simpa only [range_subtype] using hA1) hXA1 hfX
    (by simpa only [range_subtype] using hZX)
    (by simpa only [range_subtype] using hfZ) hmove
  simpa only [range_subtype] using hout
end CFSG.Quasithin.ChapterC.GlaubermanNiles
