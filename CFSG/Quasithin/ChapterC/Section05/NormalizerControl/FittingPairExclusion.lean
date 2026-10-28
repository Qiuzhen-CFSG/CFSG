module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncentralFittingExclusion
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.JankoExclusion
/-!
# The noncentral Fitting obstruction on the original pair span

The join U + Uᵍ of two elementary modules of order sixteen has binary
rank at most eight. Its actual centralizer kernel may lie inside O₂(D)
without being trivial. Applying the proved SQTK primary-core obstruction
to the literal D/O₂(D) section excludes a noncentral SL₂(5) Fitting quotient.
The final specialization uses the original A₅ block module and its proved
order; the source construction of D and its C-component remains separate.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
variable {G : Type*} [Group G] [Finite G]

/-- Apply the source obstruction to the actual two-conjugate span, retaining
both the relative centralizer and the distinct two-core quotient maps. -/
theorem pair_span_fitting_central
    {κ : GroupClass} (D : Subgroup G) (hD : IsSQTK κ D)
    (U : Subgroup G) (hU : Nat.card U = 16) (g : G)
    (hVD : U ⊔ U.conjBy g ≤ D)
    (hDV : D ≤ normalizer ((U ⊔ U.conjBy g : Subgroup G) : Set G))
    [IsElementaryAbelian 2 (U ⊔ U.conjBy g : Subgroup G)]
    (hk : centralizer ((U ⊔ U.conjBy g).subgroupOf D : Set D) ≤ pCore 2 D)
    (L : Subgroup (D ⧸ pCore 2 D)) (hL : L.IsCComponent)
    (e : (L ⧸ fittingSubgroup L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :
    fittingSubgroup L ≤ center L := by
  let V := U ⊔ U.conjBy g
  let : (V.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hVD).mpr hDV
  let : IsElementaryAbelian 2 (V.subgroupOf D) := IsElementaryAbelian.subgroupOf hVD
  have hr := four_pair_span_rank U hU g D hVD
  exact fitting_central_of_small_centralizer_quotient hD (V.subgroupOf D) hr hk L hL e

open ConjugateSource
/-- The literal original A₅ module supplies the order-sixteen hypothesis. -/
theorem alternating_pair_span_fitting_central
    {R K J : Subgroup G} (h : AlternatingPairSetup R K J)
    {κ : GroupClass} (D : Subgroup G) (hD : IsSQTK κ D) (g : G)
    (hVD : sourceModule K ⊔ (sourceModule K).conjBy g ≤ D)
    (hDV : D ≤ normalizer ((sourceModule K ⊔ (sourceModule K).conjBy g : Subgroup G) : Set G))
    [IsElementaryAbelian 2 (sourceModule K ⊔ (sourceModule K).conjBy g : Subgroup G)]
    (hk : centralizer ((sourceModule K ⊔ (sourceModule K).conjBy g).subgroupOf D : Set D) ≤ pCore 2 D)
    (L : Subgroup (D ⧸ pCore 2 D)) (hL : L.IsCComponent)
    (e : (L ⧸ fittingSubgroup L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :
    fittingSubgroup L ≤ center L :=
  pair_span_fitting_central D hD (sourceModule K) h.module_card g hVD hDV hk L hL e

/-- The original small pair span excludes every nonquasisimple
C-component of D/O₂(D), without a chosen Fitting-quotient model. -/
theorem pair_span_quasisimple
    {κ : GroupClass} (D : Subgroup G) (hD : IsSQTK κ D)
    (U : Subgroup G) (hU : Nat.card U = 16) (g : G)
    (hVD : U ⊔ U.conjBy g ≤ D)
    (hDV : D ≤ normalizer ((U ⊔ U.conjBy g : Subgroup G) : Set G))
    [IsElementaryAbelian 2 (U ⊔ U.conjBy g : Subgroup G)]
    (hk : centralizer ((U ⊔ U.conjBy g).subgroupOf D : Set D) ≤ pCore 2 D)
    (L : Subgroup (D ⧸ pCore 2 D)) (hL : L.IsCComponent) :
    IsQuasisimple L := by
  let V := U ⊔ U.conjBy g
  let : (V.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hVD).mpr hDV
  let : IsElementaryAbelian 2 (V.subgroupOf D) := IsElementaryAbelian.subgroupOf hVD
  have hr := four_pair_span_rank U hU g D hVD
  exact quasisimple_of_small_centralizer_quotient hD (V.subgroupOf D) hr hk L hL

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
