module
public import Theory.GroupTheory.RankOneInvariantKernelOrbit

/-!
# The central omega of the actual invariant normal kernel

If the core omega lies in N-alpha and has centralizer in O2(H), its
containment in W=Omega1 Z(N-alpha) forces C_S(W) into O2(H). This
centralizer is ambient-normal and alpha-invariant, hence is contained
in N-alpha by its defining maximality. The reverse inclusion is centrality.
All kernels and centralizers are those in the original group.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 7.6,
printed p.61, assertion (1).
-/

public section
open Subgroup
namespace NilesRankOneKernel
variable {H : Type*} [Group H]

theorem invariantKernel_omega_properties
    (S : Sylow 2 H) (α : MulAut S)
    (hV : omegaCenterIn (pCore 2 H) ≤
      (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype)
    (hC : centralizer (omegaCenterIn (pCore 2 H) : Set H) ≤ pCore 2 H) :
    let N := (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype
    let W := omegaCenterIn N
    N ≤ pCore 2 H ∧ omegaCenterIn (pCore 2 H) ≤ W ∧ W.Normal ∧
      (S : Subgroup H) ⊓ centralizer (W : Set H) = N := by
  let N := invariantNormalKernel (S : Subgroup H) α
  let NM := N.map (S : Subgroup H).subtype
  let W := omegaCenterIn NM
  have hNS : NM ≤ (S : Subgroup H) := map_subtype_le _
  have hNQ : NM ≤ pCore 2 H := le_sSup ⟨inferInstance,
    S.isPGroup'.of_injective (inclusion hNS) (inclusion_injective hNS)⟩
  have hVW : omegaCenterIn (pCore 2 H) ≤ W := by
    intro v hv
    obtain ⟨_,hc,hp⟩ := (mem_omegaCenterIn_iff _ _).mp hv
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨hV hv,centralizer_le hNQ hc,hp⟩
  have hWn : W.Normal := by
    apply normalizer_eq_top_iff.mp
    exact top_le_iff.mp (by
      simpa only [normalizer_eq_top] using normalizer_le_normalizer_omegaCenterIn NM)
  let C := centralizer (omegaCenterIn N : Set S)
  have hWe : (omegaCenterIn N).map (S : Subgroup H).subtype = W :=
    omegaCenterIn_map_injective _ (S : Subgroup H).subtype_injective N
  have hCe : C.map (S : Subgroup H).subtype =
      (S : Subgroup H) ⊓ centralizer (W : Set H) := by
    rw [centralizer_map_subtype,hWe]
  have hCQ : C.map (S : Subgroup H).subtype ≤ pCore 2 H := by
    rw [hCe]
    exact inf_le_right.trans ((centralizer_le hVW).trans hC)
  have hCn : (C.map (S : Subgroup H).subtype).Normal := by
    have he : C.map (S : Subgroup H).subtype =
        pCore 2 H ⊓ centralizer (W : Set H) := by
      apply le_antisymm (le_inf hCQ (hCe ▸ inf_le_right))
      rw [hCe]
      exact inf_le_inf_right _ (pCore_isPGroup.le_sylow_of_normal S)
    rw [he]
    let _ := hWn
    infer_instance
  have hCf : C.map α.toMonoidHom = C := by
    have hWf : (omegaCenterIn N).map α.toMonoidHom = omegaCenterIn N := by
      rw [omegaCenterIn_map_injective _ α.injective,invariantNormalKernel_fixed]
    apply le_antisymm
    · change (centralizer (omegaCenterIn N : Set S)).map α.toMonoidHom ≤ _
      have hh := map_centralizer_le_centralizer_image (omegaCenterIn N : Set S) α.toMonoidHom
      change (centralizer (omegaCenterIn N : Set S)).map α.toMonoidHom ≤
        centralizer ((omegaCenterIn N).map α.toMonoidHom : Set S) at hh
      rwa [hWf] at hh
    · intro x hx
      refine ⟨α.symm x,?_,α.apply_symm_apply x⟩
      intro w hw
      apply α.injective
      simpa only [map_mul,α.apply_symm_apply] using
        hx (α w) (hWf ▸ mem_map_of_mem α.toMonoidHom hw)
  have hCN : C ≤ N := le_invariantNormalKernel (S : Subgroup H) α C hCn hCf
  refine ⟨hNQ,hVW,hWn,le_antisymm (hCe ▸ map_mono hCN) ?_⟩
  apply le_inf hNS
  apply le_centralizer_iff.mpr
  intro w hw
  exact ((mem_omegaCenterIn_iff _ _).mp hw).2.1

end NilesRankOneKernel
