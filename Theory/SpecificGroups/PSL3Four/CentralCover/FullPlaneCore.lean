module

public import Theory.SpecificGroups.PSL3Four.CentralCover.FullPlaneNormalizer
public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.Commutator

/-!
# The full two-core of an actual elementary64 plane normalizer

The full normalizer is a lifted parabolic. Its actual affine projection
identifies the quotient by its two-core with SL₂(4), and order3840 makes
the full core exactly the specified elementary64 plane. The source
commutator identity therefore applies to that same plane and normalizer.
-/

namespace Matrix.PSL3Four.FullPlaneNormalizer
open Subgroup ElementaryParabolic
variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

public theorem full_plane_core
    (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker≤center E) (hk : Nat.card f.ker=4)
    (Q : Subgroup E) [IsElementaryAbelian 2 Q]
    (hkQ : f.ker≤Q) (hQ : Nat.card Q=64) :
    let N := normalizer (Q : Set E)
    N.pCoreIn 2=Q ∧ ⁅Q,N⁆=Q := by
  obtain ⟨g,b,hN⟩ := full_plane_normalizer_alignment f hf Q hkQ (by rw [hk,hQ])
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj g).surjective.comp hf
  have hker : f'.ker=f.ker := MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  have hc' : f'.ker≤center E := hker ▸ hc
  have hs (z : E) (hz : z∈f'.ker) : z^2=1 :=
    elemPow_eq_one_of_isElementaryAbelian z (hkQ (hker ▸ hz))
  let N := normalizer (Q : Set E)
  have hQcore : Q≤N.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 Q) Q.le_normalizer le_rfl
  have hNc : Nat.card N=3840 := by
    simpa only [hk] using (full_plane_normalizer f hf hc Q hkQ (by rw [hk,hQ])).2.1
  have hquot : Nat.card (N ⧸ pCore 2 N)=60 := by
    change Nat.card (normalizer (Q : Set E) ⧸ pCore 2 (normalizer (Q : Set E)))=60
    rw [hN]
    let P := liftedParabolic f' b
    let j := parabolicAffine f' b
    have hj : Function.Surjective j := parabolicAffine_surjective f' hf' b
    have hjk : IsPGroup 2 j.ker := by
      rw [parabolicAffine_ker]
      have hp : IsPGroup 2 f'.ker := IsPGroup.of_card (n := 2) (by rw [hker,hk]; decide)
      exact hp.comap_of_injective _ P.subtype_injective
    let e := (j.pCoreQuotientEquiv hj hjk).trans (Matrix.SL2.affineCoreQuotientEquiv F)
    rw [Nat.card_congr e.toEquiv,Atlas.card_sl_two,card_F]
    decide
  have hcore : Nat.card (pCore 2 N)=64 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (pCore 2 N)
    rw [hNc,hquot] at hh
    omega
  have he : N.pCoreIn 2=Q := (eq_of_le_of_card_ge hQcore (by
    rw [pCoreIn,card_map_of_injective N.subtype_injective,hcore,hQ])).symm
  refine ⟨he,?_⟩
  have hcomm : ⁅N.pCoreIn 2,N⁆=N.pCoreIn 2 := by
    change ⁅(normalizer (Q : Set E)).pCoreIn 2,normalizer (Q : Set E)⁆=
      (normalizer (Q : Set E)).pCoreIn 2
    rw [hN]
    have hh := congrArg (Subgroup.map (liftedParabolic f' b).subtype)
      (parabolicCore_commutator f' hf' hc' hs b)
    change ⁅(pCore 2 (liftedParabolic f' b)).map (liftedParabolic f' b).subtype,
      liftedParabolic f' b⁆=(pCore 2 (liftedParabolic f' b)).map (liftedParabolic f' b).subtype
    simpa only [Subgroup.map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh
  rwa [he] at hcomm

end Matrix.PSL3Four.FullPlaneNormalizer
