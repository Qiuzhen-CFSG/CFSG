module

public import CFSG.Quasithin.Chapter13.Section04.SolvableCentralizerC3
public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.Source

/-!
# Applying I.5.1(2) to the actual generated subgroup of 13.4.9

The original C₃ family in E = M ∨ C_G(z) ∨ H₀ now recognizes E without
an incidence, action, core-order or global reconstruction premise. The
remaining earlier input is the D1–D5 family constructed from 13.4.7–8.
The final fusion and product-disconnection argument proving E = G is
separate and is not assumed by the generated-subgroup conclusion.

Source: Aschbacher–Smith 13.4.9, printed pp.906–907.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section04.SolvableCentralizerC3
open Subgroup Quasithin.I5 Quasithin.I5.C3Recognition
open Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G]

def generated_equiv_sp6_of_DSystem (M H₀ : Subgroup G) (z : G)
    (S : DSystem .C3 (generated M z H₀)) : generated M z H₀ ≃* Sp (ZMod 2) :=
  equivSp6 S

def ambient_equiv_sp6_of_generated_eq_top (M H₀ : Subgroup G) (z : G)
    (S : DSystem .C3 (generated M z H₀)) (hE : generated M z H₀ = ⊤) :
    G ≃* Sp (ZMod 2) :=
  ((MulEquiv.subgroupCongr hE).trans Subgroup.topEquiv).symm.trans
    (generated_equiv_sp6_of_DSystem M H₀ z S)

end CFSG.Quasithin.Chapter13.Section04.SolvableCentralizerC3
