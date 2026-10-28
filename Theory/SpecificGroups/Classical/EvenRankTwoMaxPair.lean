module
public import Stellmacher.ElementaryAbelianMaxPair
public import Theory.SpecificGroups.PSL3Even.ThompsonProduct
public import Theory.SpecificGroups.SymplecticFour.ThompsonProduct
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings
/-! # Exact maximum elementary pairs in the binary rank-two models
Every elementary subgroup of the linear Sylow lies in one of its two root
planes; in the symplectic Sylow it lies in one of the two wings. Equal root
orders make these exactly the maximum-order family. Their literal coordinate
subgroups are retained for the Chapter 2 Thompson-product application.
Source: Aschbacher--Smith 2.5.7, printed p.555.
-/
public section
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Even.UnipotentGeometry
variable (F:Type*) [Field F] [Finite F] [CharP F 2]
theorem maxFamily_eq_planes :
    Stellmacher.elementaryAbelianMaxSubgroups (⊤:Subgroup (U F))={V₁ F,V₂ F} := by
  apply Stellmacher.maxFamily_eq_pair_of_cover _ _ _ le_top le_top
    ((card_V₁ F).trans (card_V₂ F).symm)
  intro A hA
  let : IsElementaryAbelian 2 A:=hA.2.1
  exact elementary_le_plane F A
end Matrix.PSL3Even.UnipotentGeometry
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
variable {F:Type*} [Field F] [Finite F] [CharP F 2]
theorem maxFamily_eq_wings :
    Stellmacher.elementaryAbelianMaxSubgroups (⊤:Subgroup (unipotent (F:=F)))=
      {wing false,wing true} := by
  let : Algebra (ZMod 2) F:=ZMod.algebra F 2
  let : IsElementaryAbelian 2 (wing (F:=F) false):=wing_elementary false
  let : IsElementaryAbelian 2 (wing (F:=F) true):=wing_elementary true
  apply Stellmacher.maxFamily_eq_pair_of_cover _ _ _ le_top le_top
    ((card_wing false).trans (card_wing true).symm)
  intro A hA
  let : IsElementaryAbelian 2 A:=hA.2.1
  exact SymplecticConjugatePair.elementary_le_wing A

theorem wings_ne : wing (F:=F) false≠wing true := by
  intro he
  have hx:element (1:F) 0 0 0∈wing (F:=F) false:=
    (element_mem_wing _ _ _ _ _).mpr rfl
  rw [he,element_mem_wing] at hx
  exact one_ne_zero hx
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry

