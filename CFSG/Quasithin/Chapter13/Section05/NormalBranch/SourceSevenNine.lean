module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceNine
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalQuotient

/-!
# The original ordinary conclusions (7) and (9)

The exceptional component and deleted-five model contradiction establish
O₂(LT)=V on the original source datum. Substituting that proved equality
into the maximal-subgroup and quaternion calculations gives both source
conclusions without an extra core-equality hypothesis.

Source: Aschbacher–Smith 13.5.15(7,9), printed pp.920–921.
The earlier Hypothesis 12.2.1 premise retains its 13.3.2 source producer.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSevenNine
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d hmax h e hseed hn hU

omit h e hseed hn hU in
private theorem original_maximal_twoLocal : IsMaximalTwoLocal M := by
  have hu := hmax.sylow_normalized_maximal_unique d.normalizes_L
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  rw [←d.local_normalizer] at hu
  exact hu.1

theorem source13_5_15_seven : M = D.LT ∧ D.V = M.pCoreIn 2 :=
  SourceMaximalCore.source13_5_15_seven d h e hseed hn hU
    (SourceExceptionalQuotient.original_core_eq_module d hmax h e hseed hn hU)
    (original_maximal_twoLocal d hmax)

theorem source13_5_15_nine :
    Nonempty (Section08.Source.Hstar D.H ≃* OmegaPlusFour) ∧
    ((M = D.L ∧ D.QH = D.UH) ∨
      (Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6)) ∧
        D.QH = D.UH ⊔ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)) ∧
        Nat.card ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G) : Subgroup G) = 4)) :=
  SourceNine.source13_5_15_nine d h e hseed hn hU
    (SourceExceptionalQuotient.original_core_eq_module d hmax h e hseed hn hU)
    (original_maximal_twoLocal d hmax)

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSevenNine
