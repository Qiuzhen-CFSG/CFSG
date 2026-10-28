module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.FixedResidualSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverInvolutions
public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryNineFixer

/-!
# Literal residual rows and the mixed-residual centralizer bound

The residual embedded in the ambient involution centralizer is identified
with the residual of the literal intersection. Its mixed elementary-nine row
then supplies the exact small-centralizer-action input of the transfer step.
The cover and every subgroup inclusion retain their actual maps.

Source: Aschbacher–Smith 15.3.38, printed pp.1136–1137.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel GlobalGeometry
variable {G : Type*} [Group G] [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

/-- The intrinsic intersection residual and its embedding in the involution
centralizer are the same group via the literal inclusions. -/
def graphResidualEquivIntersection (L : Subgroup G) (a : G) :
    graphResidualIn L a ≃* pResidual 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G) := by
  let C := centralizer ({a} : Set G)
  let A := L.subgroupOf C
  let e : A ≃* (L ⊓ C : Subgroup G) := {
    toFun x := ⟨x.val.val, x.property, x.val.property⟩
    invFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact ((pResidual 2 A).equivMapOfInjective A.subtype A.subtype_injective).symm.trans
    (((pResidual 2 A).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (map_pResidual 2 e)))

/-- The literal graph-centralizer intersection has its PSL₂ residual. -/
theorem graph_intersection_residual_model (h : Setup d I L) (r : LocalResult d I L)
    (b : SylowThreeLift d.T d.Y d.S L r.marking) :
    Nonempty (pResidual 2 (L ⊓ centralizer ({(b.dihedral.firstReflection : G)} : Set G) : Subgroup G) ≃*
      PSL(2,r.marking.F)) := by
  obtain ⟨e⟩ := graph_residual_model h r b
  exact ⟨(graphResidualEquivIntersection L _).symm.trans e⟩

/-- The literal field-centralizer intersection has its PSL₃(2) residual. -/
theorem field_intersection_residual_model (h : Setup d I L) (r : LocalResult d I L)
    (b : SylowThreeLift d.T d.Y d.S L r.marking) :
    Nonempty (pResidual 2 (L ⊓ centralizer ({(b.dihedral.halfTurn : G)} : Set G) : Subgroup G) ≃*
      PSL(3,ZMod 2)) := by
  obtain ⟨e⟩ := field_residual_model h r b
  exact ⟨(graphResidualEquivIntersection L _).symm.trans e⟩

/-- The literal mixed-centralizer intersection has its elementary-nine residual. -/
theorem graphField_intersection_residual_model (h : Setup d I L) (r : LocalResult d I L)
    (b : SylowThreeLift d.T d.Y d.S L r.marking) :
    Nonempty (pResidual 2 (L ⊓ centralizer
      ({(b.dihedral.firstReflection : G) * (b.dihedral.halfTurn : G)} : Set G) : Subgroup G) ≃*
      Matrix.PSL3Four.ExtendedCentralizer.ElementaryNine) := by
  obtain ⟨e⟩ := graphField_residual_model h r b
  exact ⟨(graphResidualEquivIntersection L _).symm.trans e⟩

omit [Finite G] in
/-- The ambient centralizer action on a four-cover is small whenever its
centralized subgroup is an actual elementary-nine subgroup of the cover. -/
theorem centralizerImage_card_dvd_of_elementaryNine (c : Matrix.PSL3Four.FourCover L)
    (F : Subgroup G) (hFL : F ≤ L)
    (e : F ≃* Matrix.PSL3Four.ExtendedCentralizer.ElementaryNine) :
    Nat.card (((centralizer (F : Set G)).subgroupOf
      (normalizer (L : Set G))).map L.normalizerMonoidHom) ∣ 18 :=
  (c.toCover.card_centralizerImage_dvd_quotientFixer L F c.ker_eq_center).trans
    (c.elementaryNine_quotientFixer_card_dvd (F.subgroupOf L)
      ((subgroupOfEquivOfLe hFL).trans e))

/-- The mixed residual supplies the exact cardinal divisibility needed in
source transfer, using its original ambient embedding. -/
theorem graphField_residual_centralizerImage_card_dvd (h : Setup d I L)
    (r : LocalResult d I L) (b : SylowThreeLift d.T d.Y d.S L r.marking) :
    let H := L ⊓ centralizer
      ({(b.dihedral.firstReflection : G) * (b.dihedral.halfTurn : G)} : Set G)
    let F := (pResidual 2 H).map H.subtype
    Nat.card (((centralizer (F : Set G)).subgroupOf
      (normalizer (L : Set G))).map L.normalizerMonoidHom) ∣ 18 := by
  dsimp only
  let H := L ⊓ centralizer
    ({(b.dihedral.firstReflection : G) * (b.dihedral.halfTurn : G)} : Set G)
  let F := (pResidual 2 H).map H.subtype
  obtain ⟨e⟩ := graphField_intersection_residual_model h r b
  let : Fintype r.marking.F := Fintype.ofFinite _
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let f : r.marking.F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      r.marking.card, Matrix.PSL3Four.card_F])
  let c := r.fourCover h (Atlas.fieldEquivPSL 3 f)
  exact centralizerImage_card_dvd_of_elementaryNine c F
    ((map_subtype_le _).trans inf_le_left)
    (((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm.trans e)

/-- The literal small-image premise in `Reduction.field_fusion`. -/
theorem graphField_residual_centralizerImage_not_four (h : Setup d I L)
    (r : LocalResult d I L) (b : SylowThreeLift d.T d.Y d.S L r.marking) :
    let H := L ⊓ centralizer
      ({(b.dihedral.firstReflection : G) * (b.dihedral.halfTurn : G)} : Set G)
    let F := (pResidual 2 H).map H.subtype
    ¬ 4 ∣ Nat.card (((centralizer (F : Set G)).subgroupOf
      (normalizer (L : Set G))).map L.normalizerMonoidHom) := by
  dsimp only
  intro hh
  have hd := graphField_residual_centralizerImage_card_dvd h r b
  exact (by decide : ¬ 4 ∣ 18) (hh.trans hd)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
end
