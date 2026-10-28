module

public import Theory.GroupTheory.ComponentLocalPrimeFree
public import Theory.GroupTheory.PCoreImage

/-!
# Local cores in an orbit of components

For K ≤ L with L a component and N_A(L) normalizing K, the A-conjugates
of K mutually normalize. Consequently K is normal in their join, which
is normal in ⟨K,A⟩. Its p-core therefore lies in O_p(⟨K,A⟩).

A p-element whose action on K is induced by an element of this core,
and which centralizes A, also lies in the core: its image modulo the
core is a central p-element, and the p-core lifting theorem applies.
Neither argument assumes that A fixes L.

Source application: Aschbacher–Smith 2.3.9(7), printed p.526.
-/

namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The core of a component local subgroup survives adjoining a subgroup
which may permute the components. -/
public theorem IsComponent.pCoreIn_le_local_adjoin {L K A : Subgroup G} (p : ℕ)
    (hL : IsComponent G L) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) :
    K.pCoreIn p ≤ (K ⊔ A).pCoreIn p := by
  have hn : componentOrbit K A ≤ normalizer (K : Set G) := by
    apply iSup_le
    intro a
    simpa using hL.local_conjugates_normalize hK hinv (1 : A) a
  exact (pCoreIn_mono_of_normalizes (le_componentOrbit K A) hn).trans
    (pCoreIn_mono_of_normalizes (componentOrbit_le_sup K A)
      ((normal_subgroupOf_iff_le_normalizer (componentOrbit_le_sup K A)).mp
        (componentOrbit_normal_subgroupOf_sup K A)))

/-- Ambient version for a component of a subgroup H. All normality and
component hypotheses remain relative to H. -/
public theorem IsComponent.pCoreIn_le_local_adjoin_in
    {H L K A : Subgroup G} (p : ℕ) [Fact p.Prime]
    (hLH : L ≤ H) (hAH : A ≤ H)
    (hL : IsComponent H (L.subgroupOf H)) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) :
    K.pCoreIn p ≤ (K ⊔ A).pCoreIn p := by
  have hKH : K ≤ H := hK.trans hLH
  have hn : A.subgroupOf H ⊓ normalizer (L.subgroupOf H : Set H) ≤
      normalizer (K.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hLH, ← subgroupOf_normalizer_eq hKH]
    intro x hx
    exact hinv hx
  have hc := hL.pCoreIn_le_local_adjoin p (subgroupOf_mono H hK) hn
  have hm := map_mono (f := H.subtype) hc
  have hf : IsPGroup p H.subtype.ker := IsPGroup.ker_isPGroup_of_injective H.subtype_injective
  rw [map_pCoreIn_of_ker_isPGroup H.subtype hf,
    map_pCoreIn_of_ker_isPGroup H.subtype hf, Subgroup.map_sup,
    map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hAH] at hm
  exact hm

/-- A p-element which is central modulo the core on both generating
subgroups lies in the actual p-core. -/
public theorem mem_pCore_of_inner_on_generator
    (p : ℕ) [Fact p.Prime] (K A : Subgroup G) (hgen : K ⊔ A = ⊤)
    (z t : G) (hzp : IsPGroup p (zpowers z)) (ht : t ∈ pCore p G)
    (hproj : ∀ k ∈ K, z * k * z⁻¹ = t * k * t⁻¹)
    (hcent : ∀ a ∈ A, a * z = z * a) : z ∈ pCore p G := by
  let q := QuotientGroup.mk' (pCore p G)
  have htq : q t = 1 := (QuotientGroup.eq_one_iff t).mpr ht
  have hc : (⊤ : Subgroup G) ≤ (centralizer {q z}).comap q := by
    rw [← hgen]
    apply sup_le
    · intro k hk
      change q k ∈ centralizer {q z}
      apply mem_centralizer_singleton_iff.mpr
      have he := congrArg q (hproj k hk)
      simp only [map_mul, map_inv, htq, one_mul, inv_one, mul_one] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro a ha
      exact mem_centralizer_singleton_iff.mpr (by
        simpa only [map_mul] using congrArg q (hcent a ha))
  have hzc : q z ∈ center (G ⧸ pCore p G) := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pCore p G) x
    exact mem_centralizer_singleton_iff.mp (hc (mem_top g))
  have hn : (zpowers (q z)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnc := (zpowers_le.mpr hzc : zpowers (q z) ≤ center _) hn
    simpa only [mem_center_iff.mp hnc g, mul_inv_cancel_right] using hn
  have hp : IsPGroup p (zpowers (q z)) := by
    rw [← MonoidHom.map_zpowers]
    exact hzp.map q
  have hq : q z ∈ pCore p (G ⧸ pCore p G) :=
    (le_sSup ⟨hn, hp⟩ : zpowers (q z) ≤ pCore p _) (mem_zpowers _)
  have hker : IsPGroup p q.ker := by
    change IsPGroup p (QuotientGroup.mk' (pCore p G)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have he := q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hker
  exact he ▸ hq

end Theory.GroupTheory
