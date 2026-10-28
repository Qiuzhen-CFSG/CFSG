module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.NaturalLayer
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.QuotientImages
public import Theory.GroupAction.CommonFixedNormalizer

/-!
# Earlier-clause inputs for the terminal implication of G.2.4

These records collect conclusions of clauses (1–7), including the literal
star kernel and the original upper-quotient action. They are conditional
inputs to clause (8); their construction belongs to the structure and
upper-module branches. Neither a block conclusion nor a terminal core
equality is included. The orthogonal representation remains in Hypothesis.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(1–7), printed pp.334–335.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block
open Setup
variable {G : Type*} [Group G]

/-- The structural conclusions used by the terminal branch. All cores
and images are computed in their stated containing groups. -/
structure EarlierStructure (D : Setup G) (g : G) : Prop where
  star_core : D.star D.U = (D.star D.L₁).pCoreIn 2
  star_sylow : ∃ P : Sylow 2 (D.star D.L),
    (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U
  generated : D.I g = D.L ⊔ D.U
  core_generated : D.S g = D.W g ⊔ conjugate (D.W g) g
  star_kernel : D.S g = D.I g ⊓ D.LT.pCoreIn 2
  orthogonal_intersection : D.VL ⊓ D.U = D.V
  seed_span : D.V ⊔ conjugate D.V g = D.VL
  seed_card : Nat.card D.V = 8
  orthogonal_card : Nat.card D.VL = 16
  closure_index : (D.W g).relIndex D.U = 4

theorem EarlierStructure.L_le_I {D : Setup G} {g : G}
    (c : EarlierStructure D g) : D.L ≤ D.I g := by
  rw [c.generated]
  exact le_sup_left

/-- The genuine natural model and marked images from clauses (6–7).
In the fixed-space identity U acts through its inclusion in I and the
same representative-level action as the natural model. -/
structure EarlierUpper (D : Setup G) (g : G) (c : EarlierStructure D g)
    (F : Type*) [Field F] (s : ℕ)
    [((S₂ D g).subgroupOf (D.S g)).Normal] where
  natural : NaturalLayer D g F s c.L_le_I
  complementary : IsCompl (upperImage D g (D.W g))
    (upperImage D g (conjugate (D.W g) g))
  fixed : upperImage D g (D.W g) =
    natural.action.commonFixed (D.U.subgroupOf (D.I g))
  order : Nat.card D.U = 2 ^ (2 * s + 5) * D.VL.relIndex (S₂ D g)

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block
