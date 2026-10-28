module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralPointRestriction
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedPoint
import Theory.GroupTheory.ConjugateSpanCentralizer

/-!
# The original whole module moves the central-point closure quotient

If U centralized the actual H-closure of V1 modulo <z>, it would lie in
the normal kernel of that action. This kernel normalizes V1. The proved
whole-U containment in O₂(N_G(V1)) then puts U in the two-core of this
normal kernel, hence in O₂(H). Thus the original failure U≤O₂(H) forces
nontrivial action on this same literal closure quotient.

Source: Aschbacher--Smith12.7.15, printed p.843.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The same original U acts nontrivially on the actual H-closure quotient
whenever it is not contained in the actual H two-core. -/
theorem original_tripleSix_central_point_action_nontrivial
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hHC : H ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ H.pCoreIn 2) :
    ¬ ⁅U,conjugateSpanBy (tripleSixPoint D a z) H⁆ ≤ zpowers (z:G) := by
  let V := tripleSixPoint D a z
  let Z := zpowers (z:G)
  let W := conjugateSpanBy V H
  have hs := original_tripleSix_central_point_g21_at h D a z hz hzT H hTH hHC
  have hUH : U ≤ H := D.le_sylow.trans hTH
  have hVU : V ≤ U := (tripleSixPoint_properties D a z hz).2.1
  have hVH : V ≤ H := hVU.trans hUH
  have hZV : Z ≤ V := zpowers_le.mpr (tripleSixPoint_properties D a z hz).1
  have hZH : Z ≤ H := hZV.trans hVH
  have hWH : W ≤ H := conjugateSpanBy_le_self hVH
  let : (W.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWH).mpr (le_normalizer_conjugateSpanBy V H)
  let : (Z.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hZH).mpr hs.H_le
  let A := centralizerModulo (⊤ : Subgroup H) (W.subgroupOf H) (Z.subgroupOf H)
  let : A.Normal := centralizerModulo_top_normal _ _
  let C := A.map H.subtype
  have hCH : C ≤ H := map_subtype_le _
  have hHCN : H ≤ normalizer (C : Set G) := by
    simpa only [A.normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      A.le_normalizer_map H.subtype
  have hCV : C ≤ normalizer (V : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    apply commutator_le.mpr
    rintro v hv x ⟨y,hy,rfl⟩
    exact hZV ((mem_centralizerModulo_iff.mp hy).2 ⟨v,hVH hv⟩
      (le_conjugateSpanBy V H hv))
  intro hcomm
  have hcomm' : ⁅W,U⁆ ≤ Z := by rwa [commutator_comm]
  have hUC : U ≤ C := by
    intro u hu
    refine ⟨⟨u,hUH hu⟩,mem_centralizerModulo_iff.mpr ⟨mem_top _,?_⟩,rfl⟩
    intro w hw
    exact hcomm' (commutator_mem_commutator hw hu)
  have hUcore := original_tripleSix_weightFour_point_core h structural D a z hz hzT
  exact hnot (((le_inf hUC hUcore).trans (inf_pCoreIn_le_of_le 2 hCV)).trans
    (pCoreIn_mono_of_normalizes hCH hHCN))

end CFSG.Quasithin.Chapter12.Section07
