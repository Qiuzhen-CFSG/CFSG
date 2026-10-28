module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCentralizer
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The local Sylow centralizer from the original generated-core hypothesis

For C = C_T(L), the constructed normal pair I = O²(I)V centralizes C:
its two-residual centralizes C_T(L₁), while V lies in L. Since H = L₁IT
and T normalizes C, both H and LT normalize C. The original F.9.1
assumption O₂(⟨LT,H⟩) = 1 now forces C = 1.

This proves the local-centralizer step of 13.5.15 directly on the original
source setup. No earlier maximality assertion from 13.3.2 is needed here.
Source: Aschbacher--Smith, F.9.1 and 13.5.15, printed pp.317,920.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCentralizer
open Section08.SourceCompletion
open SourcePairNormal SourcePairResidualNormal

variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬ IsMulCommutative D.UH)

include d h e hseed hn hU

/-- Original 13.5.15: C_T(L) is trivial, with every extra maximality premise
discharged by the generated-core assumption already present in F.9.1. -/
theorem sylow_local_centralizer_eq_bot_of_generated_core :
    (D.T : Subgroup G) ⊓ centralizer (D.L : Set G) = ⊥ := by
  let C := (D.T : Subgroup G) ⊓ centralizer (D.L : Set G)
  have hLC : D.L ≤ centralizer (C : Set G) :=
    le_centralizer_iff.mp (show C ≤ centralizer (D.L : Set G) from inf_le_right)
  have hTC : (D.T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf (D.T : Subgroup G).le_normalizer
      (d.normalizes_L.trans (normalizer_le_normalizer_centralizer D.L))).trans
        inf_normalizer_le_normalizer_inf
  obtain ⟨r,hrH,_,hcore,_,hgen,hI,_,hres⟩ :=
    exists_original_normal_pair d h e hseed hn hU
  let I := D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom
  change I = (pResidual 2 I).map I.subtype ⊔ D.V at hres
  have hsub : C ≤ (D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G) :=
    inf_le_inf_left _ (centralizer_le ((map_subtype_le _).trans inf_le_left))
  have hRC : (pResidual 2 I).map I.subtype ≤ centralizer (C : Set G) :=
    (residual_centralizes_local_sylow_centralizer d h e hseed hn hU I
      (pair_le h hrH) hcore hI).trans (centralizer_le hsub)
  have hVL : D.V ≤ D.L := by
    rw [← (SourceSixBlock.source13_5_15_four d h e hseed hn hU).2.1]
    exact map_subtype_le _
  have hIC : I ≤ centralizer (C : Set G) := by
    rw [hres]
    exact sup_le hRC (hVL.trans hLC)
  have hHC : D.H ≤ normalizer (C : Set G) := by
    rw [hgen]
    exact sup_le (sup_le
      (((map_subtype_le _).trans inf_le_left).trans
        (hLC.trans (centralizer_le_normalizer C)))
      (hIC.trans (centralizer_le_normalizer C))) hTC
  have hcoreC : C ≤ (D.LT ⊔ D.H : Subgroup G).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (D.T.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans (le_sup_right.trans le_sup_left))
      (sup_le (sup_le (hLC.trans (centralizer_le_normalizer C)) hTC) hHC)
  apply bot_unique
  simpa only [pCoreIn,h.generated_core,Subgroup.map_bot] using hcoreC

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCentralizer
