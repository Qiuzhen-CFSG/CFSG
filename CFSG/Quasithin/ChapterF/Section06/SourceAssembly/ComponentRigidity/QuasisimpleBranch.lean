module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity.SmallSylow

/-!
# The quasisimple conclusion of F.6.17

Apply the actual normal-component residual theorem to the literal quotient
of the original cover. When both local residuals lie in that component,
F.6.17(1) follows with no catalogue or rigidity premise. Component existence
and orientation are supplied by the independent F.6.10 source reduction.

Source: Aschbacher--Smith F.6.17, printed p.309 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {A B : Type u} [Group A] [Finite A] [Group B] [Finite B]
variable {A₁ A₂ : Subgroup A}

/-- F.6.17(1) on the original quotient once both local residuals lie in
the actual normal component selected by F.6.10. -/
theorem source_F_6_17_quasisimple_branch
    (e : A ≃* (B ⧸ pPrimeCore 3 B)) (h : IsGoldschmidtTriple A₁ A₂)
    (K : Subgroup A) [K.Normal] (hK : IsComponent A K)
    (h₁ : (pResidual 2 A₁).map A₁.subtype ≤ K)
    (h₂ : (pResidual 2 A₂).map A₂.subtype ≤ K) :
    pResidual 2 A = generalizedFitting A ∧ IsQuasisimple (pResidual 2 A) := by
  let : IsQuasisimple K := hK.2
  obtain ⟨hR, hF, hq⟩ := quasisimple_residual_of_both_local_containments h
    (Noncyclic.primeToThreeCore_eq_bot_of_quotient e) K h₁ h₂
  exact ⟨hR.trans hF.symm, hq⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
