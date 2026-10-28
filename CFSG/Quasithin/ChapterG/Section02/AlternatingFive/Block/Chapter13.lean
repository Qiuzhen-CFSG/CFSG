module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.Normality
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.Centrality
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.Terminal
public import Theory.GroupTheory.QuaternionCentralProductQuotient

/-!
# The literal terminal application in 13.5.15

The original V₁,V₃,V,L⁻,L₁,U_H,K are retained: V is the orthogonal
conjugate span and U_H=⟨V₃ᴴ⟩. Relative normality discharges the two extra
hypotheses of G.2.4(8). Its completed terminal implication then gives
K=L⁻, the intrinsic A₅-block model, O₂(K)=V and U_H=O₂(L₁)≅Q₈∘Q₈.

The factors are constructed on this same U_H, their common center is V₁,
and their multiplication gives the actual diagonal-quotient map. The
earlier conditional helpers remain available. The chapter assembly owns
the 13.5.14 setup and the remaining conclusions of 13.5.15.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.14–15, printed pp.919–920; G.2.4(8), printed pp.334–335.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Block
variable {G : Type*} [Group G] [Finite G]

/-- The core assertion in 13.5.15, conditional only on the earlier G.2.4
clauses and its two remaining terminal bounds. Relative normality supplies
the tilde commutator and local-core premises, not additional assumptions. -/
theorem chapter13_core_of_terminal_bounds
    (V₁ V₃ V Lminus T H L₁ K : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (c : EarlierStructure (chapter13Setup V₁ V₃ Lminus T H) g)
    {F : Type*} [Field F] {s : ℕ}
    [((S₂ (chapter13Setup V₁ V₃ Lminus T H) g).subgroupOf
      ((chapter13Setup V₁ V₃ Lminus T H).S g)).Normal]
    (e : EarlierUpper (chapter13Setup V₁ V₃ Lminus T H) g c F s)
    (hspan : conjugateSpanBy V₁ Lminus = V)
    (hresidual : L₁ = (chapter13Setup V₁ V₃ Lminus T H).L₁)
    (hn : (L₁.subgroupOf H).Normal)
    (hK : K = conjugateSpanBy V₃ H ⊔ conjugate (conjugateSpanBy V₃ H) g)
    (hsecond : V ⊔ (conjugateSpanBy V₃ H ⊓ conjugate (conjugateSpanBy V₃ H) g) = V)
    (hbound : K.pCoreIn 2 ≤ L₁.pCoreIn 2 ⊔ V) :
    K = Lminus ∧ K.pCoreIn 2 = V ∧
      conjugateSpanBy V₃ H ≤ L₁.pCoreIn 2 ∧ Nat.card (conjugateSpanBy V₃ H) = 32 := by
  let D := chapter13Setup V₁ V₃ Lminus T H
  have hVL : D.VL = V := hspan
  have hKI : K = D.I g := hK
  have hn' : (D.L₁.subgroupOf D.H).Normal := hresidual ▸ hn
  obtain ⟨hfull, hcore⟩ := d.terminal_premises_of_local_normal hn'
  have hS₂ : S₂ D g = D.VL := by
    change D.VL ⊔ (D.U ⊓ conjugate D.U g) = D.VL
    rw [hVL]
    exact hsecond
  have hbound' : D.S g ≤ D.L₁.pCoreIn 2 ⊔ D.VL := by
    change (D.I g).pCoreIn 2 ≤ D.L₁.pCoreIn 2 ⊔ D.VL
    rw [← hKI, ← hresidual, hVL]
    exact hbound
  have hS := d.core_eq_first_of_terminal_bounds c e hcore hS₂ hbound'
  refine ⟨hKI.trans (d.terminal_group_eq hfull c.generated), ?_, ?_,
    Hypothesis.closure_card_of_core_eq_first (D := D) (g := g) c hS⟩
  · exact congrArg (fun A : Subgroup G => A.pCoreIn 2) hKI |>.trans (hS.trans hVL)
  · rw [hresidual]
    exact (d.terminal_reduction hfull).2

/-- The identified closure in 13.5.15 is compared to the diagonal quotient
through its actual factors, retaining both factor embeddings in the formula. -/
theorem chapter13_diagonal_quotient_of_factors (V₃ H : Subgroup G)
    (q : QuaternionCentralProductData (conjugateSpanBy V₃ H))
    (eL : q.left ≃* QuaternionGroup 2) (eR : q.right ≃* QuaternionGroup 2) :
    ∃ e : QuaternionCentralProduct.Model ≃* conjugateSpanBy V₃ H,
      ∀ x y : QuaternionGroup 2,
        e (QuotientGroup.mk' QuaternionCentralProduct.diagonalCenter (x, y)) =
          eL.symm x * eR.symm y :=
  q.exists_quotientEquiv eL eR

/-- The G.2.4(8) application on printed p.920. Only the earlier clauses and
the identities of the original source groups are retained as inputs.
Relative normality supplies both terminal premises. -/
theorem chapter13_terminal_block
    (V₁ V₃ V Lminus T H L₁ U_H K : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (c : EarlierStructure (chapter13Setup V₁ V₃ Lminus T H) g)
    {F : Type*} [Field F] {s : ℕ}
    [((S₂ (chapter13Setup V₁ V₃ Lminus T H) g).subgroupOf
      ((chapter13Setup V₁ V₃ Lminus T H).S g)).Normal]
    (e : EarlierUpper (chapter13Setup V₁ V₃ Lminus T H) g c F s)
    (hspan : conjugateSpanBy V₁ Lminus = V)
    (hresidual : L₁ = (chapter13Setup V₁ V₃ Lminus T H).L₁)
    (hn : (L₁.subgroupOf H).Normal)
    (hU : U_H = conjugateSpanBy V₃ H)
    (hK : K = U_H ⊔ conjugate U_H g) :
    K = Lminus ∧ ChapterC.IsAlternatingBlock K 5 ∧ K.pCoreIn 2 = V ∧
      U_H = ⁅U_H, L₁⁆ ∧ U_H = L₁.pCoreIn 2 ∧
      Nonempty (QuaternionCentralProductData U_H) ∧
      Nonempty (U_H ≃* QuaternionCentralProduct.Model) := by
  let D := chapter13Setup V₁ V₃ Lminus T H
  have hVL : D.VL = V := hspan
  have hKI : K = D.I g := by
    rw [hU] at hK
    exact hK
  have hn' : (D.L₁.subgroupOf D.H).Normal := hresidual ▸ hn
  obtain ⟨hfull, hcore⟩ := d.terminal_premises_of_local_normal hn'
  obtain ⟨hI, hS, hblock, hlocal, hq, hmodel⟩ := d.terminal_block c e hfull hcore
  have hKL : K = Lminus := hKI.trans hI
  refine ⟨hKL, hKL.symm ▸ hblock, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun A : Subgroup G => A.pCoreIn 2) hKI).trans (hS.trans hVL)
  · rw [hU, hresidual]
    exact (d.U_commutator_of_local_normal hn').symm
  · rw [hU, hresidual]
    exact hlocal
  · rw [hU]
    exact hq
  · rw [hU]
    exact hmodel

/-- The actual U_H has two quaternion factors with common center V₁.
The displayed map preserves both factor embeddings in the original closure. -/
theorem chapter13_terminal_quaternion_presentation
    (V₁ V₃ Lminus T H L₁ U_H : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (c : EarlierStructure (chapter13Setup V₁ V₃ Lminus T H) g)
    {F : Type*} [Field F] {s : ℕ}
    [((S₂ (chapter13Setup V₁ V₃ Lminus T H) g).subgroupOf
      ((chapter13Setup V₁ V₃ Lminus T H).S g)).Normal]
    (e : EarlierUpper (chapter13Setup V₁ V₃ Lminus T H) g c F s)
    (hresidual : L₁ = (chapter13Setup V₁ V₃ Lminus T H).L₁)
    (hn : (L₁.subgroupOf H).Normal)
    (hU : U_H = conjugateSpanBy V₃ H) :
    ∃ q : QuaternionCentralProductData U_H,
      (q.left ⊓ q.right).map U_H.subtype = V₁ ∧
      ∃ (eL : q.left ≃* QuaternionGroup 2) (eR : q.right ≃* QuaternionGroup 2)
        (f : QuaternionCentralProduct.Model ≃* U_H),
        ∀ x y : QuaternionGroup 2,
          f (QuotientGroup.mk' QuaternionCentralProduct.diagonalCenter (x, y)) =
            eL.symm x * eR.symm y := by
  subst U_H
  subst L₁
  obtain ⟨hfull, hcore⟩ := d.terminal_premises_of_local_normal hn
  exact d.terminal_quaternion_presentation c e hfull hcore

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
