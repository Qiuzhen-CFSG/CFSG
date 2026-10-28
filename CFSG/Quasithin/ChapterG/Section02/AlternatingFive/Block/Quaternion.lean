module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.Quaternion.Factors

/-!
# The local core and quaternion central product in G.2.4(8)

Under the two source terminal premises and the separately proved collapse
S=V_L, the original U equals O₂(L₁) and has genuine quaternion factors.
Their multiplication identifies U with (Q₈×Q₈)/⟨(-1,-1)⟩. The proof uses
the actual orthogonal coordinates, the exact star kernel, G.2.2 centrality,
and the normal elementary seed of order eight. It assumes no block recognition.

The source's core collapse, block conclusion, and literal §13.5 assembly
remain with the terminal theorem's owner; the collapse is an explicit input here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(8), printed pp.334–335, with the central-product convention E.2.16,
printed p.228.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Hypothesis
open Setup Block
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- The quaternion branch of G.2.4(8), conditional precisely on its two
terminal premises and the intermediate collapse S=V_L. -/
theorem terminal_local_core_and_quaternion (d : Hypothesis D g)
    (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hcore : D.L₁.pCoreIn 2 ≤ D.QH) (hS : D.S g = D.VL) :
    D.U = D.L₁.pCoreIn 2 ∧ Nonempty (QuaternionCentralProductData D.U) ∧
      Nonempty (D.U ≃* QuaternionCentralProduct.Model) :=
  ⟨Quaternion.closure_eq_local_core d c hfull hcore hS,
    Quaternion.closure_quaternion_factors d c hfull hS,
    Quaternion.closure_quaternion_model d c hfull hS⟩

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Hypothesis
