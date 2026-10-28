module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.ChapterF.Section09.Setup
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Assembly.Chapter13

/-!
# The nine conclusions of 13.5.15

This is a conclusion contract, not a hypothesis for the source theorem.
Its eventual constructor must assume the genuine §13.5 setup, nonabelian
U_H, local normality of L₁ in H, and the exclusion of the triple cover
L/O₂(L) ≅ A-hat₆. The preceding source alternatives then distinguish
ordinary A₅ and A₆. In particular no exclusion of U₄(3) is appropriate.

All starred images use H/O₂(H); barred images use LT/O₂(LT).
The quotient M/O₂(M) in clauses (8–9) is literally M/V after clause (7).
Quaternion squares mean the central product Q₈∘Q₈, not Q₈×Q₈.
The product in (9ii) is a join with C_T(L₁), as in the source's
normalizing product. The orthogonal plus group Ω₄⁺(2) is represented
by its concrete S₃×S₃ model; the quotient alternatives are equivalences,
not unconnected family tags.

The separate `MarkedBlockInput` is exactly the earlier substitution
needed from 13.5.14. It contains no block or quaternion conclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.5.14–15, printed pp.919–921 (PDF pp.936–938).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch
open ChapterG.Section02.AlternatingFive
variable {G : Type*} [Group G]

def K (D : ChapterF.Section09.Setup G) (g : G) : Subgroup G :=
  D.UH ⊔ ChapterG.Section02.Setup.conjugate D.UH g

/-- The source O²(O₂(LT)K), with the residual taken inside that join. -/
def blockResidual (D : ChapterF.Section09.Setup G) (g : G) : Subgroup G :=
  let J := D.LT.pCoreIn 2 ⊔ K D g
  (pResidual 2 J).map J.subtype

abbrev S3 := Equiv.Perm (Fin 3)
abbrev C3 := Multiplicative (ZMod 3)
abbrev FourGroup := Multiplicative (Fin 2 → ZMod 2)
abbrev OmegaPlusFour := S3 × S3

/-- All nine source conclusions; proving only a field does not prove 13.5.15. -/
structure Conclusions (D : ChapterF.Section09.Setup G) (M : Subgroup G)
    (n : ℕ) (g : G) : Prop where
  one : D.UH = ⁅D.UH, D.L₁⁆ ∧ D.UH ≤ D.L ∧
    Nonempty (Section08.Source.starImage D.H D.L₁ ≃* C3)
  two : D.g2.star D.UH = (D.g2.star D.L₁).pCoreIn 2 ∧
    Nonempty (D.g2.star D.UH ≃* FourGroup)
  three : ChapterC.IsAlternatingBlock (K D g) 5 ∧ K D g ≤ D.L
  four : (n = 5 → D.L = K D g ∧ ChapterC.IsAlternatingBlock D.L 5) ∧
    (n = 6 → ChapterC.IsAlternatingBlock D.L 6)
  five : D.L₁.pCoreIn 2 = D.UH ∧
    Nonempty (D.UH ≃* QuaternionCentralProduct.Model)
  six : D.H = D.Gz ∧
    Section08.Source.Hz D.L₁ D.T D.Gz M = {D.Gz}
  seven : M = D.LT ∧ D.V = M.pCoreIn 2
  eight : n = 5 → D.QH = D.UH ∧
    (∃ f : Section08.Source.Hstar D.H →* OmegaPlusFour, Function.Injective f) ∧
    ((M = D.L ∧ Nonempty (Section08.Source.Hstar D.H ≃* S3 × C3)) ∨
      (Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 5)) ∧
        Nonempty (Section08.Source.Hstar D.H ≃* OmegaPlusFour)))
  nine : n = 6 → Nonempty (Section08.Source.Hstar D.H ≃* OmegaPlusFour) ∧
    ((M = D.L ∧ D.QH = D.UH) ∨
      (Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6)) ∧
        D.QH = D.UH ⊔ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)) ∧
        Nat.card ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G) : Subgroup G) = 4))

/-- The marked source output of 13.5.14, before G.2.4(8) is applied. -/
structure MarkedBlockInput [Finite G] (D : ChapterF.Section09.Setup G)
    (n : ℕ) (g : G) where
  marked : Hypothesis (chapter13Setup D.V₁ D.Vplus (blockResidual D g) D.T D.H) g
  span : conjugateSpanBy D.V₁ (blockResidual D g) = D.V
  residual : D.L₁ = (chapter13Setup D.V₁ D.Vplus (blockResidual D g) D.T D.H).L₁
  inside : blockResidual D g ≤ D.L
  five_eq : n = 5 → D.L = blockResidual D g

end CFSG.Quasithin.Chapter13.Section05.NormalBranch
end
