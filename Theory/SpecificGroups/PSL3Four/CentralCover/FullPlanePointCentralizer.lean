module

public import Theory.SpecificGroups.PSL3Four.CentralCover.FullPlaneCore
import Theory.SpecificGroups.SL2.NaturalStabilizer

/-!
# Noncentral point centralizers in the actual elementary-plane parabolic

The affine image of a noncentral element of the elementary64 plane is a
nonzero translation. Its SL₂(4) stabilizer is a two-group, as is the full
central covering kernel. Thus its whole centralizer in the plane parabolic
is a two-group. No order-only identification of a cover is used.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3Four.FullPlaneNormalizer
open ElementaryParabolic

private theorem affine_nonzero_translation_centralizer
    (x : Matrix.SL2.Affine F) (hx : x∈Matrix.SL2.translations F) (hne : x≠1) :
    IsPGroup 2 (centralizer ({x} : Set (Matrix.SL2.Affine F))) := by
  rw [←Matrix.SL2.range_inl_eq_translations] at hx
  obtain ⟨v,rfl⟩ := hx
  have hv : v.toAdd≠0 := by
    intro he
    have hv1 : v=1 := Multiplicative.toAdd.injective he
    exact hne (by rw [hv1,map_one])
  let q : Matrix.SL2.Affine F→*SL(2,F) := SemidirectProduct.rightHom
  have hk : IsPGroup 2 q.ker := by
    rw [←SemidirectProduct.range_inl_eq_ker_rightHom,Matrix.SL2.range_inl_eq_translations,
      ←Matrix.SL2.affine_twoCore_eq]
    exact pCore_isPGroup
  have hp := (Matrix.SL2.stabilizer_nonzero_isPGroup v.toAdd hv).comap_of_ker_isPGroup q hk
  suffices hle : centralizer ({SemidirectProduct.inl v} : Set (Matrix.SL2.Affine F))≤
      (MulAction.stabilizer SL(2,F) v.toAdd).comap q from
    hp.of_injective (inclusion hle) (inclusion_injective hle)
  intro g hg
  have he := congrArg SemidirectProduct.left (mem_centralizer_singleton_iff.mp hg)
  change g.left * Matrix.SL2.naturalAction F g.right v = v * Matrix.SL2.naturalAction F 1 g.left at he
  rw [map_one,MulAut.one_apply,mul_comm v g.left] at he
  have hfix := congrArg Multiplicative.toAdd (mul_left_cancel he)
  exact hfix

/-- A point of the elementary plane outside the full central kernel has a
two-group centralizer in its whole parabolic normalizer. -/
theorem full_plane_point_centralizer_isPGroup
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E→*PSL) (hf : Function.Surjective f)
    (hc : f.ker≤center E) (hk : Nat.card f.ker=4)
    (Q : Subgroup E) [IsElementaryAbelian 2 Q]
    (hkQ : f.ker≤Q) (hQ : Nat.card Q=64)
    (z : E) (hz : z∈Q) (hzn : z∉f.ker) :
    IsPGroup 2 (normalizer (Q : Set E)⊓centralizer ({z} : Set E) : Subgroup E) := by
  obtain ⟨g,b,hN⟩ := full_plane_normalizer_alignment f hf Q hkQ (by rw [hk,hQ])
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj g).surjective.comp hf
  have hker : f'.ker=f.ker := MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  let N := liftedParabolic f' b
  let j := parabolicAffine f' b
  have hj : Function.Surjective j := parabolicAffine_surjective f' hf' b
  have hjk : IsPGroup 2 j.ker := by
    rw [parabolicAffine_ker]
    exact (IsPGroup.of_card (p := 2) (n := 2) (by rw [hker,hk]; decide)).comap_of_injective
      N.subtype N.subtype_injective
  have hcore : (pCore 2 N).map N.subtype=Q := by
    have hh := (full_plane_core f hf hc hk Q hkQ hQ).1
    change (normalizer (Q : Set E)).pCoreIn 2=Q at hh
    rwa [hN] at hh
  have hQN : Q≤N := by rw [←hcore]; exact map_subtype_le _
  let zN : N := ⟨z,hQN hz⟩
  have hzcore : zN∈pCore 2 N := by
    have he : Q.subgroupOf N=pCore 2 N := by
      change Q.comap N.subtype=pCore 2 N
      rw [←hcore,comap_map_eq_self_of_injective N.subtype_injective]
    exact he ▸ hz
  have hzj : j zN∈Matrix.SL2.translations F := by
    rw [←Matrix.SL2.affine_twoCore_eq]
    change zN∈(pCore 2 (Matrix.SL2.Affine F)).comap j
    rw [j.comap_pCore_of_ker_isPGroup hj hjk]
    exact hzcore
  have hzjn : j zN≠1 := by
    intro he
    have hh : zN∈j.ker := he
    rw [parabolicAffine_ker] at hh
    exact hzn (hker ▸ hh)
  have hp := (affine_nonzero_translation_centralizer (j zN) hzj hzjn).comap_of_ker_isPGroup j hjk
  have hC : IsPGroup 2 (centralizer ({zN} : Set N)) := by
    suffices hle : centralizer ({zN} : Set N)≤(centralizer ({j zN} : Set (Matrix.SL2.Affine F))).comap j from
      hp.of_injective (inclusion hle) (inclusion_injective hle)
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul] using congrArg j (mem_centralizer_singleton_iff.mp hx))
  rw [hN]
  have hm : (centralizer ({zN} : Set N)).map N.subtype=N⊓centralizer ({z} : Set E) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc)),rfl⟩
  exact hm ▸ hC.map N.subtype

end Matrix.PSL3Four.FullPlaneNormalizer
