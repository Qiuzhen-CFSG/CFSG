module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Source
public import Theory.GroupTheory.TwoLayerCentralizer

/-!
# Two-layer rigidity in the original H-action

G.2.2(4) says that the actual image of U/V₁ in H/V₁ is two-reduced.
For any H-invariant subgroup B of that image, the automorphisms fixing B
and the quotient by B form a normal two-group in the faithful actor image.
Reducedness therefore makes them fix all of U/V₁. This applies the existing
two-layer displacement argument to the literal tilde groups, rather than
to the distinct starred L-action.

This is an input to a possible elimination of extra central constituents;
no assertion about those constituents is made here.

Source: Aschbacher–Smith, G.2.2(4) and G.2.6, printed pp.332 and 336.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- A simultaneous fixer of two invariant layers in the literal reduced
H-module fixes the whole module. -/
theorem Hypothesis.tilde_two_layer_rigidity (d : Hypothesis D g)
    (B : Subgroup (D.tilde D.H)) [B.Normal]
    (hB : B ≤ (D.tilde D.U).subgroupOf (D.tilde D.H)) :
    centralizer (B : Set (D.tilde D.H)) ⊓
        commutatorPreimage ⊤ ((D.tilde D.U).subgroupOf (D.tilde D.H)) B ≤
      centralizer (((D.tilde D.U).subgroupOf (D.tilde D.H)) : Set (D.tilde D.H)) := by
  let A := (D.tilde D.U).subgroupOf (D.tilde D.H)
  let : A.Normal := d.closure.reduced.normal
  let : IsElementaryAbelian 2 A := d.closure.reduced.elementary
  have hBp : IsPGroup 2 B := (IsElementaryAbelian.isPGroup 2 A).of_injective
    (inclusion hB) (inclusion_injective hB)
  exact two_layer_le_radical A B (centralizer (A : Set (D.tilde D.H)))
    hBp d.closure.reduced.quotient_pCore_eq_bot inf_le_right

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
