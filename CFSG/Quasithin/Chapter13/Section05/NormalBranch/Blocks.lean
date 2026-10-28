module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.Defs
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.Initial

/-!
# The block and quaternion deductions on the original §13.5 data

Apply 13.5.14 only after the original F.9 normality argument has supplied
its tilde-commutator premise. G.2.4 then proves the A₅ block, the exact
O₂(L₁), and the quaternion presentation with common center the original
V₁. We also retain the exact H/O₂(H) kernel intersection and the A₅
case L=K. These are parts of 13.5.15, not its full nine-clause result.

The earlier marked substitution remains explicit, as does the genuine
universal G.1.3 recognition input. Their producers are the §13.5 local
geometry and G.1 owners. No desired block or quaternion assertion is
an assumption of the earlier substitution.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.5.15(1,3–5), printed pp.919–920 (PDF pp.936–937).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch
open ChapterG.Section02.AlternatingFive
open Recognition Recognition.ProjectiveGeometry
universe u
variable {G : Type u} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {n : ℕ} {g : G}

/-- Partial source output, including the marked center and the actual core kernel. -/
theorem block_consequences (h : D.Hypothesis)
    (hseed : D.Vplus = ⁅D.V, D.L₁⁆)
    (hn : (D.L₁.subgroupOf D.H).Normal)
    (hearlier : D.tilde D.UH = ⁅D.tilde D.UH, D.tilde D.L₁⁆ →
      Nonempty (MarkedBlockInput D n g))
    (hrec : RecognitionInput.{0,u} F4) :
    D.UH = ⁅D.UH, D.L₁⁆ ∧ D.UH ≤ D.L ∧
      ChapterC.IsAlternatingBlock (K D g) 5 ∧ K D g ≤ D.L ∧
      (K D g).pCoreIn 2 = D.V ∧ D.L₁.pCoreIn 2 = D.UH ∧
      D.L₁ ⊓ D.QH = D.UH ∧ Nat.card D.UH = 32 ∧
      Nonempty (D.UH ≃* QuaternionCentralProduct.Model) ∧
      (n = 5 → D.L = K D g ∧ ChapterC.IsAlternatingBlock D.L 5) ∧
      ∃ q : QuaternionCentralProductData D.UH,
        (q.left ⊓ q.right).map D.UH.subtype = D.V₁ := by
  obtain ⟨b⟩ := hearlier (tilde_closure_commutator h hseed hn)
  obtain ⟨hK, hblock, hcoreK, hc, hcoreL, _, hiso⟩ :=
    chapter13_block_of_local_normal D.V₁ D.Vplus D.V (blockResidual D g)
      D.T D.H D.L₁ D.UH (K D g) g b.marked hrec b.span b.residual hn rfl rfl
  obtain ⟨q, hpoint, _⟩ := chapter13_quaternion_of_local_normal
    D.V₁ D.Vplus (blockResidual D g) D.T D.H D.L₁ D.UH g
      b.marked hrec b.residual hn rfl
  refine ⟨hc, (closure_reduction h hseed hn).2.2, hblock, hK ▸ b.inside,
    hcoreK, hcoreL.symm, (local_core_intersection h hn).trans hcoreL.symm,
    q.card, hiso, ?_, q, hpoint⟩
  intro hn5
  have he : D.L = K D g := (b.five_eq hn5).trans hK.symm
  exact ⟨he, he ▸ hblock⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch
end
