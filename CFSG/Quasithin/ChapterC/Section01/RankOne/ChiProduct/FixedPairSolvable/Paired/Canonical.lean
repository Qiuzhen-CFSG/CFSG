module
public import Theory.GroupTheory.PResidual.ConjugateSpan
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Kernel
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Parabolic
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup

/-!
# Geometry of the canonical Baumann conjugate span

Put N=⟨Baum(T)^L⟩ for the actual source factor preimage L. The normal
residual--Baumann join contains N, so its original Baumann Sylow restricts
to N. If L contains the ambient two-core, N is normal in a characteristic
two overgroup and is itself characteristic two. Its full original action
kernel centralizes the intrinsic omega-center span. The embedded residual
is subnormal in the original ambient group when L is subnormal there.

No minimality or Frattini bound is inherited by an arbitrary subgroup.
Source: Aschbacher--Smith C.1.26 and B.6.10, printed pp.132,117.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Paired
open ChapterB SelectedRankOne
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

theorem canonical_baumann_sylow (T : Sylow 2 G) (L : Subgroup G)
    (hB : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (pResidual 2 G ⊔ baumann (T : Subgroup G))) :
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (conjugateSpanBy (baumann (T : Subgroup G)) L) := by
  let E := pResidual 2 G ⊔ baumann (T : Subgroup G)
  let : E.Normal := baumann_residual_join_normal (T : Subgroup G) (pResidual 2 G)
    (pResidual_sup_sylow_eq_top T)
  exact Chapter1.IsSylowIn.restrict hB (le_conjugateSpanBy _ _)
    (conjugateSpanBy_le le_sup_right le_normalizer_of_normal)

theorem canonical_baumann_fitting (T : Sylow 2 G) (L : Subgroup G)
    (hfit : generalizedFitting G = pCore 2 G) (hcore : pCore 2 G ≤ L) :
    generalizedFitting (conjugateSpanBy (baumann (T : Subgroup G)) L) =
      pCore 2 (conjugateSpanBy (baumann (T : Subgroup G)) L) := by
  let B := baumann (T : Subgroup G)
  let N := conjugateSpanBy B L
  let P := L ⊔ B
  have hNP : N ≤ P := conjugateSpanBy_le le_sup_right
    (le_sup_left.trans P.le_normalizer)
  let : (N.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hNP).mpr
    (conjugateSpanBy_normalized_by_join B L)
  have hP := centralizer_pCore_le_of_pCore_le P
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit) (hcore.trans le_sup_left)
  exact (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hNP)).mp
      (normal_core_selfCentralizing hP (N.subgroupOf P)))

/-- The original action kernel is retained, including its odd part. -/
theorem canonical_kernel_centralizes_omegaClosure (T : Sylow 2 G)
    (q : G →* Q)
    (hk : (pResidual 2 G ⊔ baumann (T : Subgroup G)) ⊓ q.ker ≤
      centralizer (thompsonAlpha (T : Subgroup G) : Set G))
    (L : Subgroup G)
    (S : Sylow 2 (conjugateSpanBy (baumann (T : Subgroup G)) L))
    (hS : (S : Subgroup (conjugateSpanBy (baumann (T : Subgroup G)) L)).map
      (conjugateSpanBy (baumann (T : Subgroup G)) L).subtype = baumann (T : Subgroup G)) :
    (q.comp (conjugateSpanBy (baumann (T : Subgroup G)) L).subtype).ker ≤
      centralizer (normalClosure (omegaOneCenterAmbient
        (S : Subgroup (conjugateSpanBy (baumann (T : Subgroup G)) L)) :
          Set (conjugateSpanBy (baumann (T : Subgroup G)) L)) :
            Set (conjugateSpanBy (baumann (T : Subgroup G)) L)) := by
  let E := pResidual 2 G ⊔ baumann (T : Subgroup G)
  let : E.Normal := baumann_residual_join_normal (T : Subgroup G) (pResidual 2 G)
    (pResidual_sup_sylow_eq_top T)
  exact restricted_kernel_centralizes_omegaClosure T q hk _
    (conjugateSpanBy_le le_sup_right le_normalizer_of_normal) S hS

/-- Subnormality is proved for the canonical residual, in the original group. -/
theorem canonical_residual_subnormal (T : Sylow 2 G) (L : Subgroup G)
    (hBL : baumann (T : Subgroup G) ≤ normalizer (L : Set G)) (hL : L.IsSubnormal) :
    ((pResidual 2 (conjugateSpanBy (baumann (T : Subgroup G)) L)).map
      (conjugateSpanBy (baumann (T : Subgroup G)) L).subtype).IsSubnormal :=
  embedded_residual_conjugateSpanBy_subnormal _ L (T.isPGroup'.to_le inf_le_left) hBL hL
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Paired
