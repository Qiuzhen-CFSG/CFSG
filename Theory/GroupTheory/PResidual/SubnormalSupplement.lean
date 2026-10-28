module

public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Mathlib.GroupTheory.IsSubnormal

/-!
# Subnormal p-perfect subgroups with a p-subgroup supplement

A subnormal p-perfect subgroup X in a product XR, with R a p-group, is the
p-residual of XR. Along a subnormal chain, the residual of each term is X:
characteristicness makes X normal in the next term, and the product supplies
its p-group quotient. No finiteness assumption is required for this argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.4.2(2), printed p. 57.
-/

open scoped Pointwise
namespace Subgroup

/-- A subnormal p-perfect subgroup with a p-group supplement is the residual. -/
public theorem pResidual_eq_of_subnormal_product {G : Type*} [Group G] {p : ℕ} (X R : Subgroup G)
    (hsub : X.IsSubnormal) (hX : IsPPerfect p X) (hR : IsPGroup p R)
    (hprod : ∀ g : G, ∃ x ∈ X, ∃ r ∈ R, x * r = g) :
    pResidual p G = X := by
  obtain ⟨n, F, hmono, hnorm, hzero, hn⟩ := hsub.exists_chain
  have hXF (i : ℕ) : X ≤ F i := hzero ▸ hmono (Nat.zero_le i)
  have hmain (i : ℕ) : (pResidual p (F i)).map (F i).subtype = X := by
    induction i with
    | zero =>
      rw [hzero, (pResidual_eq_top_iff p X).mpr hX]
      simpa only [← MonoidHom.range_eq_map] using X.range_subtype
    | succ i ih =>
      have hNX : F (i + 1) ≤ normalizer X := by
        rw [← ih]
        exact (normal_subgroupOf_iff_le_normalizer (hmono (Nat.le_succ i))).mp (hnorm i) |>.trans
          (normalizer_le_normalizer_characteristic_image (F i) (pResidual p (F i)))
      let : (X.subgroupOf (F (i + 1))).Normal := normal_subgroupOf_of_le_normalizer hNX
      have hXp : IsPPerfect p (X.subgroupOf (F (i + 1))) :=
        hX.of_surjective (subgroupOfEquivOfLe (hXF (i + 1))).symm.toMonoidHom
          (subgroupOfEquivOfLe (hXF (i + 1))).symm.surjective
      have hRp : IsPGroup p (R.subgroupOf (F (i + 1))) := hR.comap_subtype
      have hsup : X.subgroupOf (F (i + 1)) ⊔ R.subgroupOf (F (i + 1)) = ⊤ := by
        apply eq_top_iff.mpr
        intro g _
        obtain ⟨x, hx, r, hr, he⟩ := hprod g
        have hrF : r ∈ F (i + 1) := by
          have ht := (F (i + 1)).mul_mem ((F (i + 1)).inv_mem (hXF (i + 1) hx)) g.property
          rw [← he, inv_mul_cancel_left] at ht
          exact ht
        have he' : (⟨x, hXF (i + 1) hx⟩ : F (i + 1)) * ⟨r, hrF⟩ = g := Subtype.ext he
        rw [← he']
        exact mul_mem (mem_sup_left hx) (mem_sup_right hr)
      rw [pResidual_eq_of_isPPerfect_sup _ _ hXp hRp hsup, map_subgroupOf_eq_of_le (hXF _)]
  have h := hmain n
  rw [hn] at h
  change (pResidual p (⊤ : Subgroup G)).map (Subgroup.topEquiv.toMonoidHom) = X at h
  rwa [map_pResidual] at h

/-- Permutable subgroups have their set product as their join. -/
public theorem coe_sup_of_set_mul_comm {G : Type*} [Group G] (X R : Subgroup G)
    (hc : (X : Set G) * (R : Set G) = (R : Set G) * (X : Set G)) :
    (↑(X ⊔ R) : Set G) = (X : Set G) * (R : Set G) := by
  apply Set.Subset.antisymm
  · rw [sup_eq_closure_mul]
    intro g hg
    induction hg using closure_induction'' with
    | mem _ hx => exact hx
    | one => exact ⟨1, X.one_mem, 1, R.one_mem, mul_one 1⟩
    | inv_mem a ha =>
      obtain ⟨x, hx, r, hr, rfl⟩ := ha
      rw [hc, mul_inv_rev]
      exact Set.mul_mem_mul (R.inv_mem hr) (X.inv_mem hx)
    | mul a b _ _ ha hb =>
      obtain ⟨x, hx, r, hr, rfl⟩ := ha
      obtain ⟨y, hy, s, hs, rfl⟩ := hb
      obtain ⟨z, hz, t, ht, he⟩ := Set.mem_mul.mp (hc.symm ▸ Set.mul_mem_mul hr hy)
      refine ⟨x * z, X.mul_mem hx hz, t * s, R.mul_mem ht hs, ?_⟩
      calc
        x * z * (t * s) = x * (z * t) * s := by group
        _ = x * r * (y * s) := by rw [he]; group
  · rintro g ⟨x, hx, r, hr, rfl⟩
    exact mul_mem (mem_sup_left hx) (mem_sup_right hr)

end Subgroup
