module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalOddRadical
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The normal restricted actor group

For a normal kernel subgroup K, set P=L1T and R=O2(P). The subgroup E=KR is
normal in X=KP: P normalizes both K and R, while K lies in E. Moreover E/K is
a two-group. These literal source subgroups are the restriction used by the
rank-one FF-action argument in the original plus-kernel proof.

Source: Aschbacher--Smith 13.7.4(1), printed p.937.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

theorem source_kernel_radical_join_normal
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    {K : Subgroup G}
    (hKH : K ≤ H) (hKn : H ≤ normalizer (K : Set G)) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let P := F.L₁ ⊔ (T : Subgroup G)
    let R := P.pCoreIn 2
    let X := K ⊔ P
    let E := K ⊔ R
    E ≤ X ∧ X ≤ normalizer (E : Set G) ∧
      (E.subgroupOf X).Normal ∧
      ∃ hn : (K.subgroupOf E).Normal, letI := hn; IsPGroup 2 (E ⧸ K.subgroupOf E) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let P := F.L₁ ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let X := K ⊔ P
  let E := K ⊔ R
  have hEH : E ≤ H := sup_le hKH ((pCoreIn_le 2 P).trans h.local_le)
  have hEX : E ≤ X := sup_le le_sup_left ((pCoreIn_le 2 P).trans le_sup_right)
  have hPR : P ≤ normalizer (R : Set G) := P.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hPE : P ≤ normalizer (E : Set G) :=
    (le_inf (h.local_le.trans hKn) hPR).trans
      (normalizer_inf_normalizer_le_normalizer_sup K R)
  have hXE : X ≤ normalizer (E : Set G) :=
    sup_le ((show K ≤ E from le_sup_left).trans E.le_normalizer) hPE
  let : (E.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer hXE
  let : (K.subgroupOf E).Normal := normal_subgroupOf_of_le_normalizer (hEH.trans hKn)
  refine ⟨hEX,hXE,inferInstance,inferInstance,?_⟩
  have hgen : K.subgroupOf E ⊔ R.subgroupOf E = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ E from le_sup_left) (show R ≤ E from le_sup_right)]
    exact subgroupOf_self E
  exact isPGroup_quotient_of_sup_eq_top _ _ (isPGroup_pCoreIn 2 P).comap_subtype hgen

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
