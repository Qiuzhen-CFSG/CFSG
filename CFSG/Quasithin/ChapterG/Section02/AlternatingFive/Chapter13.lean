module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Layers

/-!
# The literal orthogonal layers used in §13.5

In 13.5.14 the seed V₃ replaces G.2's V, whereas the ambient orthogonal
module V replaces V_L. This substitution keeps the original H-closure
U_H=⟨V₃ᴴ⟩ and the original conjugator. The earlier chapter owner supplies
the source hypothesis and V=⟨V₁ᴸ⁻⟩; G.2.4(2) supplies L⁻≤K.

The elementary layer below is used in the final contradiction of 13.5.25.
It does not assert block recognition in 13.5.15, which additionally needs
the terminal argument of G.2.4(8).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.14, 13.5.22 and 13.5.25, printed pp.919,924–925.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
variable {G : Type*} [Group G]

def chapter13Setup (V₁ V₃ Lminus T H : Subgroup G) : Setup G where
  V := V₃
  V₁ := V₁
  L := Lminus
  T := T
  H := H

/-- Elementary abelianness of the actual V(U_H∩U_Hᵍ) in 13.5.25. -/
theorem chapter13_second_layer_elementary [Finite G]
    (V₁ V₃ V Lminus T H : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hspan : conjugateSpanBy V₁ Lminus = V)
    (hgen : Lminus ≤ conjugateSpanBy V₃ H ⊔ conjugate (conjugateSpanBy V₃ H) g) :
    IsElementaryAbelian 2
      (V ⊔ (conjugateSpanBy V₃ H ⊓ conjugate (conjugateSpanBy V₃ H) g) : Subgroup G) := by
  have he := d.second_elementary hgen
  change IsElementaryAbelian 2
    (conjugateSpanBy V₁ Lminus ⊔
      (conjugateSpanBy V₃ H ⊓ conjugate (conjugateSpanBy V₃ H) g) : Subgroup G) at he
  rwa [hspan] at he

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
