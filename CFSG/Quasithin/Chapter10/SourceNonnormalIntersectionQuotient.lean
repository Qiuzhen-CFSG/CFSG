module
public import CFSG.Quasithin.Chapter10.SourceNonnormalIntersectionComponent
public import Theory.GroupTheory.PCoreCoverEquiv

/-!
# Quotient marking of the original covering intersection component

The literal component LH = (L ∩ H)^∞ covers L modulo its two-core.
Consequently its own two-core quotient identifies with L/O₂(L), by
the original inclusion. In particular the original A₅ marking transfers
to LH without asserting that LH is an A₅ block or a component of H.

Source: Aschbacher–Smith, 4.2.12 and its use of C.2.8–C.4.8,
printed pp.610–611 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

/-- The source intersection component inherits the original two-core
quotient through its actual inclusion in L. -/
theorem source_covering_intersection_quotient
    {I H : Subgroup G} (hIM : I ≤ D.maximalLocal) (hIH : I ≤ H)
    (hcover : (localOrbit T L : Set G) ⊆
      (I : Set G) * ((localOrbit T L).pCoreIn 2 : Set G)) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ eH : (LH ⧸ pCore 2 LH) ≃* (L ⧸ pCore 2 L),
      ∀ x : LH, eH (QuotientGroup.mk' (pCore 2 LH) x) =
        QuotientGroup.mk' (pCore 2 L)
          ⟨x.val, ((map_subtype_le _).trans inf_le_left) x.property⟩ := by
  exact exists_pCoreQuotientEquiv_of_cover
    ((map_subtype_le _).trans inf_le_left)
    (source_covering_intersection_component D hIM hIH hcover).2.subset

/-- The A₅ quotient marking of L induces a marking of the literal LH,
with the original quotient map on representatives. -/
theorem source_a5_covering_intersection_quotient
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I H : Subgroup G} (hIM : I ≤ D.maximalLocal) (hIH : I ≤ H)
    (hcover : (localOrbit T L : Set G) ⊆
      (I : Set G) * ((localOrbit T L).pCoreIn 2 : Set G)) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ eH : (LH ⧸ pCore 2 LH) ≃* alternatingGroup (Fin 5),
      ∀ x : LH, eH (QuotientGroup.mk' (pCore 2 LH) x) =
        e (QuotientGroup.mk' (pCore 2 L)
          ⟨x.val, ((map_subtype_le _).trans inf_le_left) x.property⟩) := by
  obtain ⟨eH, heH⟩ := source_covering_intersection_quotient D hIM hIH hcover
  exact ⟨eH.trans e, fun x => congrArg e (heH x)⟩
end CFSG.Quasithin.Chapter10
