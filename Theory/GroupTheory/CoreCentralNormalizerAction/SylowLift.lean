module

public import Theory.GroupTheory.CoreCentralNormalizerAction
public import Theory.GroupTheory.SylowNormalizerCentralQuotient

/-!
# Recovering the original Sylow from its core-central image

A Sylow subgroup is uniquely determined by its image under a central
quotient, even when the central kernel has odd order. The preceding full
two-core quotient also preserves this uniqueness, since the two-core lies
in every Sylow two-subgroup. Equivariance of the literal normalizer action
therefore lifts stabilization of the core-central Sylow image to actual
normalization of the original ambient Sylow subgroup.

No centrality of the composite core-central kernel is assumed.
Source application: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory

private theorem sylow_eq_of_central_image_eq
    {G H : Type*} [Group G] [Group H] [Finite G]
    {p : ℕ} [Fact p.Prime] (P Q : Sylow p G)
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ center G)
    (he : (P : Subgroup G).map f = (Q : Subgroup G).map f) : P=Q := by
  have hPN : (P : Subgroup G) ≤ normalizer (Q : Set G) := by
    rw [←Q.normalizer_comap_of_central_kernel f hf hk]
    intro x hx
    change f x ∈ normalizer ((Q : Subgroup G).map f : Set H)
    apply (Q : Subgroup G).map f |>.le_normalizer
    rw [←he]
    exact mem_map_of_mem f hx
  have hPQ : (P : Subgroup G) ≤ Q := by
    have hh := P.isPGroup'.inf_normalizer_sylow Q
    rw [inf_eq_left.mpr hPN] at hh
    exact inf_eq_left.mp hh.symm
  exact Sylow.ext (P.is_maximal' Q.isPGroup' hPQ).symm

private theorem sylow_eq_of_coreCentral_image_eq
    {G : Type*} [Group G] [Finite G] (K : Subgroup G) (P Q : Sylow 2 K)
    (he : (P : Subgroup K).map (coreCentralProjection K) =
      (Q : Subgroup K).map (coreCentralProjection K)) : P=Q := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let z := QuotientGroup.mk' (center (K ⧸ pCore 2 K))
  let Pq := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let Qq := Q.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hmap : (Pq : Subgroup (K ⧸ pCore 2 K)).map z =
      (Qq : Subgroup (K ⧸ pCore 2 K)).map z := by
    change ((P : Subgroup K).map q).map z = ((Q : Subgroup K).map q).map z
    simpa only [coreCentralProjection,q,z,map_map] using he
  have hPQ := sylow_eq_of_central_image_eq Pq Qq z (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) hmap
  have hm : (P : Subgroup K).map q = (Q : Subgroup K).map q :=
    congrArg Sylow.toSubgroup hPQ
  have hkerP : q.ker ≤ P := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  have hkerQ : q.ker ≤ Q := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal Q
  apply Sylow.ext
  have hh := congrArg (fun R => R.comap q) hm
  simpa only [comap_map_eq_self hkerP,comap_map_eq_self hkerQ] using hh

/-- Stabilizing the literal Sylow image in K/O₂(K)/Z forces normalization
of the original supplied Sylow in the original ambient group. -/
theorem coreCentral_stabilizer_normalizes_sylow
    {G : Type*} [Group G] [Finite G] (K A : Subgroup G) (U : Sylow 2 K)
    (hAK : A ≤ normalizer (K : Set G))
    (hstab : coreCentralActorImage K A ≤
      MulAction.stabilizer (MulAut (coreCentralQuotient K))
        ((U : Subgroup K).map (coreCentralProjection K))) :
    A ≤ normalizer ((U : Subgroup K).map K.subtype : Set G) := by
  intro a ha
  let x : normalizer (K : Set G) := ⟨a,hAK ha⟩
  let α := K.normalizerMonoidHom x
  let β := normalizerCoreCentralAction K x
  let q := coreCentralProjection K
  have hs := hstab (mem_map_of_mem (normalizerCoreCentralAction K)
    (show x ∈ A.subgroupOf (normalizer (K : Set G)) from ha))
  change ((U : Subgroup K).map q).map β.toMonoidHom = (U : Subgroup K).map q at hs
  let P := U.mapSurjective (f := α.toMonoidHom) α.surjective
  have he : q.comp α.toMonoidHom = β.toMonoidHom.comp q := by
    ext u
    exact (normalizerCoreCentralAction_apply K x u).symm
  have hPU : (P : Subgroup K).map q = (U : Subgroup K).map q := by
    change ((U : Subgroup K).map α.toMonoidHom).map q = _
    rw [map_map,he,←map_map,hs]
  have hP := sylow_eq_of_coreCentral_image_eq K P U hPU
  have hα : (U : Subgroup K).map α.toMonoidHom = U := congrArg Sylow.toSubgroup hP
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_map]
  have heG : (MulAut.conj a : G →* G).comp K.subtype = K.subtype.comp α.toMonoidHom := by
    ext u
    rfl
  rw [heG,←map_map,hα]

end Theory.GroupTheory
