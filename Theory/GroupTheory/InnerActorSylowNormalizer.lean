module
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Mathlib.GroupTheory.Sylow
public import Theory.GroupTheory.SubgroupConjugateIncidence
/-!
# Inner actors and Sylow subgroups of a subgroup normalizer

When a centerless subgroup has only inner automorphisms, an ambient two-group
normalizing it and a marked subgroup has unique inner representatives. These
representatives lie in one Sylow subgroup of the marked subgroup normalizer.
Every intrinsic overgroup of that Sylow is therefore normalized by the original
ambient actor. This preserves the actor when selecting a local overgroup.

Source application: Aschbacher--Smith 2.4.25, printed p.543.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem exists_inner_normalizer_sylow
    (K L R : Subgroup G)
    (hRK : R ≤ normalizer (K : Set G))
    (hRL : R ≤ normalizer (L : Set G)) (hR : IsPGroup 2 R)
    (hc : center K = ⊥)
    (hi : Function.Surjective (MulAut.conj : K →* MulAut K)) :
    ∃ P : Sylow 2 (normalizer (L.subgroupOf K : Set K)),
      ∀ N : Subgroup K,
        (P : Subgroup (normalizer (L.subgroupOf K : Set K))).map
          (normalizer (L.subgroupOf K : Set K)).subtype ≤ N →
        R ≤ normalizer (N.map K.subtype : Set G) := by
  let e : K ≃* MulAut K := MulEquiv.ofBijective (MulAut.conj : K →* MulAut K)
    ⟨MulAut.conj_injective_of_center_eq_bot hc,hi⟩
  let a : R →* MulAut K := K.normalizerMonoidHom.comp (inclusion hRK)
  let f : R →* K := e.symm.toMonoidHom.comp a
  have he (r : R) (x : K) :
      ((f r * x * (f r)⁻¹ : K) : G) = (r : G) * (x : G) * (r : G)⁻¹ := by
    have hh := congrArg (fun b : MulAut K => b x) (e.apply_symm_apply (a r))
    exact congrArg Subtype.val hh
  let B := normalizer (L.subgroupOf K : Set K)
  have hf (r : R) : f r ∈ B := by
    apply mem_normalizer_iff.mpr
    intro x
    change (x : G) ∈ L ↔ ((f r * x * (f r)⁻¹ : K) : G) ∈ L
    rw [he]
    exact mem_normalizer_iff.mp (hRL r.property) x
  let fB : R →* B := f.codRestrict B hf
  have hp : IsPGroup 2 fB.range := hR.of_surjective fB.rangeRestrict
    fB.rangeRestrict_surjective
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  refine ⟨P,?_⟩
  intro N hPN r hr
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨v,hv,rfl⟩
    have hfr : f ⟨r,hr⟩ ∈ N := hPN (mem_map_of_mem B.subtype
      (hP (show fB ⟨r,hr⟩ ∈ fB.range from ⟨⟨r,hr⟩,rfl⟩)))
    exact ⟨f ⟨r,hr⟩ * v * (f ⟨r,hr⟩)⁻¹,
      N.mul_mem (N.mul_mem hfr hv) (N.inv_mem hfr),he ⟨r,hr⟩ v⟩
  · intro hx
    have hri := R.inv_mem hr
    have hfr : f ⟨r⁻¹,hri⟩ ∈ N := hPN (mem_map_of_mem B.subtype
      (hP (show fB ⟨r⁻¹,hri⟩ ∈ fB.range from ⟨⟨r⁻¹,hri⟩,rfl⟩)))
    obtain ⟨v,hv,hvG⟩ := hx
    have hm : ((f ⟨r⁻¹,hri⟩ * v * (f ⟨r⁻¹,hri⟩)⁻¹ : K) : G) = x := by
      rw [he]
      change r⁻¹ * K.subtype v * (r⁻¹)⁻¹ = x
      rw [hvG]
      simp [mul_assoc]
    exact ⟨_,N.mul_mem (N.mul_mem hfr hv) (N.inv_mem hfr),hm⟩
end Theory.GroupTheory

