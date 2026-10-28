module

public import Theory.GroupTheory.PResidual.PerfectCover
public import Mathlib.GroupTheory.Frattini

/-!
# Frattini generation from an image of the prime residual

Let L = Oᵖ(G) in a finite group. If the image of L under a homomorphism f
lies in the image of I, preservation and monotonicity of residuals show
L = Oᵖ(I)(L ∩ ker f), with Oᵖ(I) embedded in G. If the latter kernel has
Frattini image in L/N, nongeneration gives L ≤ IN.

No normality of I is assumed. The proof takes the residual before passing
to L/N, so all groups in the Frattini argument are actual subgroups of L.
This is the residual step in Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined manuscript of 1 March 2004, proof of B.2.18,
printed p.80.
-/

namespace Subgroup
variable {G K : Type*} [Group G] [Group K] [Finite G]

/-- Taking residuals preserves the covering of the ambient residual by an image. -/
public theorem pResidual_eq_embedded_sup_kernel_of_map_le (p : ℕ) (I : Subgroup G) (f : G →* K)
    (h : (pResidual p G).map f ≤ I.map f) :
    pResidual p G = (pResidual p I).map I.subtype ⊔ (pResidual p G ⊓ f.ker) := by
  let L := pResidual p G
  let D := (pResidual p I).map I.subtype
  have hDL : D ≤ L := map_pResidual_le p I.subtype
  have hres : (pResidual p L).map L.subtype = L := by
    rw [(pResidual_eq_top_iff p L).mpr (isPPerfect_pResidual p)]
    rw [← MonoidHom.range_eq_map, L.range_subtype]
  have hm := embedded_pResidual_mono p h
  rw [← map_embedded_pResidual, ← map_embedded_pResidual, hres] at hm
  have hcover : L ≤ D ⊔ f.ker := by
    simpa only [comap_map_eq] using
      (le_comap_map f L).trans (comap_mono hm)
  apply le_antisymm _ (sup_le hDL inf_le_left)
  intro x hx
  obtain ⟨d, hd, c, hc, rfl⟩ := mem_sup_of_normal_right.mp (hcover hx)
  have hcL : c ∈ L := by
    simpa using L.mul_mem (L.inv_mem (hDL hd)) hx
  exact mul_mem_sup hd ⟨hcL, hc⟩

/-- Frattini nongeneration removes the image kernel modulo a normal subgroup
of the residual. -/
public theorem pResidual_le_sup_of_frattini_kernel (p : ℕ) (I : Subgroup G) (f : G →* K)
    (N : Subgroup (pResidual p G)) [N.Normal]
    (h : (pResidual p G).map f ≤ I.map f)
    (hker : pResidual p G ⊓ f.ker ≤
      ((frattini ((pResidual p G) ⧸ N)).comap (QuotientGroup.mk' N)).map
        (pResidual p G).subtype) :
    pResidual p G ≤ I ⊔ N.map (pResidual p G).subtype := by
  let L := pResidual p G
  let D := (pResidual p I).map I.subtype
  let C := L ⊓ f.ker
  let q := QuotientGroup.mk' N
  have hDL : D ≤ L := map_pResidual_le p I.subtype
  have hDC : D ⊔ C = L := (pResidual_eq_embedded_sup_kernel_of_map_le p I f h).symm
  have htop : D.subgroupOf L ⊔ C.subgroupOf L = ⊤ := by
    apply map_injective L.subtype_injective
    rw [map_sup, map_subgroupOf_eq_of_le hDL,
      map_subgroupOf_eq_of_le (show C ≤ L from inf_le_left), hDC,
      ← MonoidHom.range_eq_map, L.range_subtype]
  have hC : (C.subgroupOf L).map q ≤ frattini (L ⧸ N) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := hker hx
    have hxy : y = x := Subtype.ext he
    exact hxy ▸ hy
  have hgen : (D.subgroupOf L).map q ⊔ frattini (L ⧸ N) = ⊤ := by
    apply top_unique
    have hm := congrArg (map q) htop
    rw [map_sup, map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at hm
    exact hm.symm.le.trans (sup_le_sup_left hC _)
  have hDtop := frattini_nongenerating hgen
  have hDN : D.subgroupOf L ⊔ N = ⊤ := by
    have hm := congrArg (comap q) hDtop
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hm
  have hDeq : D ⊔ N.map L.subtype = L := by
    have hm := congrArg (map L.subtype) hDN
    rwa [map_sup, map_subgroupOf_eq_of_le hDL,
      ← MonoidHom.range_eq_map, L.range_subtype] at hm
  exact hDeq.symm.le.trans (sup_le_sup_right (map_subtype_le _) _)
end Subgroup
