module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.Reduction
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup

/-!+# The actual parabolic subgroups for the inner K.3.4 degree estimate

The two radicals retain their original embeddings in Sp₄(F). Their distinguished
root subgroups are roots 0 and 4 in the existing matrix convention. Each radical
has q³ elements and each root subgroup q elements. These cardinalities are the
numerical inputs to the offender enlargement argument; no representation
recognition or conjugate-generation assertion is included in these definitions.

Source: Guralnick--Malle, *Classification of 2F-modules II*, Proposition 6.2,
part 1A, author manuscript pp.38--39; Aschbacher--Smith K.3.4, printed p.457.
-/

@[expose] public section
open Subgroup Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.InnerDegree

variable {F : Type*} [Field F] [CharP F 2]

/-- False denotes the point radical; true denotes the plane radical. -/
noncomputable def radical (i : Bool) : Subgroup (Sp F) :=
  if i then planeRadicalAmbient else pointRadicalAmbient

/-- The point radical's central long root and the plane radical's central short root. -/
def centralRoot (i : Bool) : Subgroup (Sp F) :=
  RootSubgroup.group (if i then 4 else 0)

private def pointCoordinates : pointRadical (F := F) ≃ F × F × F where
  toFun q := (q.val.val.val (.inl 1) (.inr 0), q.val.val.val (.inr 1) (.inr 0),
    q.val.val.val (.inl 0) (.inr 0))
  invFun x := ⟨pointRadicalElement x.1 x.2.1 x.2.2, pointRadicalElement_mem _ _ _⟩
  left_inv q := Subtype.ext (pointRadical_eq_element q.val q.property).symm
  right_inv _ := rfl

/-- The literal embedded radical has three field coordinates. -/
theorem card_radical [Finite F] (i : Bool) :
    Nat.card (radical (F := F) i) = Nat.card F ^ 3 := by
  cases i
  · change Nat.card (pointRadical.map pointLocal.subtype) = _
    rw [card_map_of_injective pointLocal.subtype_injective,
      Nat.card_congr (pointCoordinates (F := F)), Nat.card_prod, Nat.card_prod]
    ring
  · change Nat.card (Plane.radical.map planeLocal.subtype) = _
    rw [card_map_of_injective planeLocal.subtype_injective, EvenTwoRank.card_plane_radical]

omit [CharP F 2] in
/-- Both distinguished roots have one field coordinate. -/
theorem card_centralRoot (i : Bool) : Nat.card (centralRoot (F := F) i) = Nat.card F :=
  RootSubgroup.card _

end CFSG.Quasithin.ChapterK.Symplectic.Recognition.InnerDegree
