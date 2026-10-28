module

public import Theory.GroupTheory.PStar.Basic

/-!
# Residual Sylow-centralizer supplements

In a p-perfect finite group, a supplement to a normal subgroup can be
replaced by its p-residual. Map the supplement onto the quotient, use
surjective preservation of residuals, and pull back the resulting cover.
Applying this to the p-star definition gives its residual formulation.

Source: GLS II, Chapter B, the remarks following Definition 5.1.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {p : ℕ} {G : Type*} [Group G] [Finite G]

/-- A normal supplement in a p-perfect group can be replaced by its p-residual. -/
theorem sup_embedded_pResidual_eq_top (hG : IsPPerfect p G)
    (N C : Subgroup G) [N.Normal] (hgen : N ⊔ C = ⊤) :
    N ⊔ (pResidual p C).map C.subtype = ⊤ := by
  let q := QuotientGroup.mk' N
  have hC : C.map q = ⊤ := by
    have h := congrArg (Subgroup.map q) hgen
    simpa [Subgroup.map_sup, q,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] using h
  let f := q.comp C.subtype
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp (by
    simpa only [f, MonoidHom.range_comp, range_subtype] using hC)
  have hres : (pResidual p C).map f = ⊤ := by
    rw [map_pResidual_of_surjective p f hf,
      (pResidual_eq_top_iff p _).mpr (hG.of_surjective q (QuotientGroup.mk'_surjective N))]
  have himage : ((pResidual p C).map C.subtype).map q = ⊤ := by
    rwa [map_map]
  have h := congrArg (Subgroup.comap q) himage
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top, sup_comm] using h

/-- The residual form of the defining Sylow-centralizer supplement (GLS II 5.1). -/
theorem IsPStar.sup_pResidual_centralizer_eq_top (hG : IsPStar p G)
    (N : Subgroup G) [N.Normal] (P : Sylow p N) :
    N ⊔ (pResidual p (centralizer ((P : Subgroup N).map N.subtype : Set G))).map
      (centralizer ((P : Subgroup N).map N.subtype : Set G)).subtype = ⊤ :=
  sup_embedded_pResidual_eq_top ((pResidual_eq_top_iff p G).mp hG.1) N _ (hG.2 N P)
end Theory.GroupTheory
