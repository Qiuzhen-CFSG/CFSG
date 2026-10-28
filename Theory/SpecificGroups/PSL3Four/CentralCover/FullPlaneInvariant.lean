module

public import Theory.SpecificGroups.PSL3Four.CentralCover.FullPlaneCore
public import Theory.SpecificGroups.SL2.Affine.InvariantPreimage

/-!
# Proper invariant subgroups of an elementary64 plane

The actual plane normalizer induces the full affine action. Its natural
translation quotient is irreducible, and the plane is its commutator with
the normalizer. Thus a proper invariant subgroup lies in the original
central covering kernel.
-/

namespace Matrix.PSL3Four.FullPlaneNormalizer
open Subgroup ElementaryParabolic
variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

public theorem full_plane_invariant
    (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker≤center E) (hk : Nat.card f.ker=4)
    (Q : Subgroup E) [IsElementaryAbelian 2 Q]
    (hkQ : f.ker≤Q) (hQ : Nat.card Q=64)
    (A : Subgroup E) (hAQ : A≤Q)
    (hNA : normalizer (Q : Set E)≤normalizer (A : Set E)) :
    A≤f.ker ∨ A=Q := by
  obtain ⟨g,b,hN⟩ := full_plane_normalizer_alignment f hf Q hkQ (by rw [hk,hQ])
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj g).surjective.comp hf
  have hker : f'.ker=f.ker := MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  have hc' : f'.ker≤center E := hker ▸ hc
  let P := liftedParabolic f' b
  let j := parabolicAffine f' b
  have hj : Function.Surjective j := parabolicAffine_surjective f' hf' b
  have hjk : IsPGroup 2 j.ker := by
    rw [parabolicAffine_ker]
    have hp : IsPGroup 2 f'.ker := IsPGroup.of_card (n := 2) (by rw [hker,hk]; decide)
    exact hp.comap_of_injective _ P.subtype_injective
  have hjc : j.ker≤center P := by
    intro x hx
    have hx' : (x:E)∈f'.ker := by
      simpa only [j,parabolicAffine_ker,mem_comap,Subgroup.subtype_apply] using hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hc' hx') y)
  have hpre : (Matrix.SL2.translations F).comap j=pCore 2 P := by
    rw [←Matrix.SL2.affine_twoCore_eq]
    exact j.comap_pCore_of_ker_isPGroup hj hjk
  have hcore : (pCore 2 P).map P.subtype=Q := by
    have hh := (full_plane_core f hf hc hk Q hkQ hQ).1
    change (normalizer (Q : Set E)).pCoreIn 2=Q at hh
    rwa [hN] at hh
  have hQP : Q≤P := by
    rw [←hcore]
    exact map_subtype_le _
  have hsub : Q.subgroupOf P=pCore 2 P := by
    change Q.comap P.subtype=pCore 2 P
    rw [←hcore,comap_map_eq_self_of_injective P.subtype_injective]
  have hn : P≤normalizer (A : Set E) := by
    change liftedParabolic f' b≤normalizer (A : Set E)
    rwa [hN] at hNA
  let : (A.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hn
  have hs (z:E) (hz:z∈f'.ker) : z^2=1 :=
    elemPow_eq_one_of_isElementaryAbelian z (hkQ (hker ▸ hz))
  have hcomm : ⁅(Matrix.SL2.translations F).comap j,(⊤ : Subgroup P)⁆=
      (Matrix.SL2.translations F).comap j := by
    rw [hpre]
    exact parabolicCore_commutator f' hf' hc' hs b
  have hApre : A.subgroupOf P≤(Matrix.SL2.translations F).comap j := by
    rw [hpre,←hsub]
    exact comap_mono hAQ
  rcases Matrix.SL2.invariant_preimage_le_kernel_or_eq j hj hjc hcomm
      (A.subgroupOf P) hApre with hz | he
  · left
    intro x hx
    have hh := hz (show (⟨x,hQP (hAQ hx)⟩:P)∈A.subgroupOf P from hx)
    have hx' : x∈f'.ker := by
      simpa only [j,parabolicAffine_ker,mem_comap,Subgroup.subtype_apply] using hh
    exact hker ▸ hx'
  · right
    have hh := congrArg (Subgroup.map P.subtype) he
    rwa [map_subgroupOf_eq_of_le (hAQ.trans hQP),hpre,hcore] at hh

end Matrix.PSL3Four.FullPlaneNormalizer
