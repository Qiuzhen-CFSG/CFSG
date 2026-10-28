module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Source
public import CFSG.Quasithin.Chapter12.Section08.Defs

/-!
# The G.2.5 intersection in the binary natural flag

For a marked three-dimensional flag the seed and point are exactly V and
V₁ from Section 12.8, and the H-closure is its original U. Applying the
source intersection theorem therefore uses the original marked g and h,
and normality is relative to their generated group.

The natural-action setup is supplied by the earlier Section 12.8 source
owner. The containment U≤T and Frattini bound are the precise conclusions
of 12.8.4/G.2.2. The full series and its recognition still require the
remaining clauses of G.2.5.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5(4–5) and 12.8.8(4–5), printed pp.335,851–852.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open CFSG.Quasithin.Chapter12.Section08

variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}

/-- The literal substitution used for the three-dimensional binary flag. -/
def binarySetup (F : InvariantFlag T V 3) (L : Subgroup G) : Setup G where
  V := V
  V₁ := F.Vi 1
  L := L
  T := T
  H := F.H

/-- The normal elementary intersection and its full commutator bound on
the original Section 12.8 groups, before the later collapse S₂=V. -/
theorem binary_flag_intersection [Finite G] (F : InvariantFlag T V 3)
    (L : Subgroup G) (g h : G)
    (d : Hypothesis (binarySetup F L) (ZMod 2) 1 g h)
    (hUT : F.U ≤ (T : Subgroup G))
    (hf : (frattini F.U).map F.U.subtype ≤ F.Vi 1) :
    let J := (F.U ⊔ conjugate F.U g) ⊔ conjugate F.U h
    let E := (F.U ⊓ conjugate F.U g) ⊓ conjugate F.U h
    V ≤ E ∧ E ≤ J.pCoreIn 2 ∧ (E.subgroupOf J).Normal ∧
      ⁅E, J⁆ ≤ V ∧ IsElementaryAbelian 2 E :=
  d.intersection hUT hf

/-- The natural-action proof of centrality specializes to the original
binary flag as soon as G.2.5(2) places L in the generated group. -/
theorem binary_flag_central_first [Finite G] (F : InvariantFlag T V 3)
    (L : Subgroup G) (g h : G)
    (d : Hypothesis (binarySetup F L) (ZMod 2) 1 g h)
    (hUT : F.U ≤ (T : Subgroup G))
    (hL : L ≤ (F.U ⊔ conjugate F.U g) ⊔ conjugate F.U h) :
    let J := (F.U ⊔ conjugate F.U g) ⊔ conjugate F.U h
    V ≤ J.pCoreIn 2 ⊓ centralizer (J.pCoreIn 2 : Set G) :=
  d.central_first hUT hL

end CFSG.Quasithin.ChapterG.Section02.LinearThree
