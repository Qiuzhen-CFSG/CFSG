module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.SecondAction
public import Theory.GroupTheory.DihedralRelations
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# A computable model of the actual second binary Ree endpoint

The verified radical action and the two generating involutions define an
explicit semidirect product of the radical by the dihedral group of order six.
The literal endpoint inclusion gives a surjective homomorphism. Its domain and
the actual endpoint both have order 12288, so this map is an isomorphism.
No calculation in the ambient Ree matrix group is needed for its injectivity.

Source: the marked second parabolic and twelve Weyl relations in
`FullRee.SecondExtension`, used for the reflection-pair census of F.4.8.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.PointedPairs
open ReeTwo SecondExtension Theory.GroupTheory

noncomputable abbrev radicalMap : radical →* Endpoint := inclusion.comp radical.subtype

local instance : radical.Normal := by
  change radicalCharacter.ker.Normal
  infer_instance

def firstRootAction : MulAut radical := MulAut.conjNormal (SylowModel.root 0)
def rotationAction : MulAut radical := firstRootAction * secondWeyl

noncomputable def rotation : Endpoint := inclusion (SylowModel.root 0) * reflection

theorem radicalMap_firstRootAction (x : radical) :
    radicalMap (firstRootAction x) =
      inclusion (SylowModel.root 0) * radicalMap x * (inclusion (SylowModel.root 0))⁻¹ := by
  change inclusion (SylowModel.root 0 * x.val * (SylowModel.root 0)⁻¹) = _
  simp only [map_mul, map_inv]
  rfl

theorem radicalMap_secondWeyl (x : radical) :
    radicalMap (secondWeyl x) = reflection * radicalMap x * reflection⁻¹ :=
  inclusion_secondWeylWord x

theorem radicalMap_rotationAction (x : radical) :
    radicalMap (rotationAction x) = rotation * radicalMap x * rotation⁻¹ := by
  change radicalMap (firstRootAction (secondWeyl x)) = _
  rw [radicalMap_firstRootAction, radicalMap_secondWeyl]
  unfold rotation
  group

theorem firstRootAction_square : firstRootAction ^ 2 = 1 := by
  change (MulAut.conjNormal (H := radical) (SylowModel.root 0)) ^ 2 = 1
  rw [← map_pow, show SylowModel.root 0 ^ 2 = 1 from by decide +kernel, map_one]

theorem secondWeyl_square : secondWeyl ^ 2 = 1 := by
  apply MulEquiv.ext
  intro x
  change secondWeyl (secondWeyl x) = x
  exact secondWeyl.left_inv x

theorem rotationAction_cube : rotationAction ^ 3 = 1 := by
  apply MulEquiv.ext
  intro x
  simp only [show (3 : Nat) = 2+1 from rfl, pow_succ, MulAut.mul_apply, MulAut.one_apply]
  apply Subtype.ext
  apply inclusion_injective
  change radicalMap (rotationAction (rotationAction (rotationAction x))) = radicalMap x
  rw [radicalMap_rotationAction, radicalMap_rotationAction, radicalMap_rotationAction]
  calc
    _ = rotation^3 * radicalMap x * (rotation^3)⁻¹ := by simp only [pow_succ, pow_zero]; group
    _ = _ := by rw [show rotation^3=1 from weyl_relations.cube]; simp

theorem product_inverted {M : Type*} [Group M] (a b : M)
    (ha : a^2=1) (hb : b^2=1) : b*(a*b)*b⁻¹=(a*b)⁻¹ := by
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha)
  have hbi : b⁻¹=b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hb)
  rw [mul_inv_rev, hai]
  calc
    b*(a*b)*b⁻¹=b*a := by group
    _=b⁻¹*a := by rw [hbi]

def secondAction : DihedralGroup 3 →* MulAut radical :=
  DihedralRelations.ofRelations rotationAction secondWeyl rotationAction_cube
    secondWeyl_square (product_inverted firstRootAction secondWeyl
      firstRootAction_square secondWeyl_square)

noncomputable def secondSection : DihedralGroup 3 →* Endpoint :=
  DihedralRelations.ofRelations rotation reflection weyl_relations.cube
    weyl_relations.square (product_inverted (inclusion (SylowModel.root 0)) reflection
      (by rw [← map_pow, show SylowModel.root 0 ^ 2 = 1 from by decide +kernel, map_one])
      weyl_relations.square)

theorem radicalMap_rotation_pow (n : Nat) (x : radical) :
    radicalMap ((rotationAction^n) x) = rotation^n * radicalMap x * (rotation^n)⁻¹ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change radicalMap (rotationAction ((rotationAction^n) x)) = _
    rw [radicalMap_rotationAction, ih, pow_succ']
    group

theorem secondAction_compatible (g : DihedralGroup 3) (x : radical) :
    radicalMap (secondAction g x) = secondSection g * radicalMap x * (secondSection g)⁻¹ := by
  cases g with
  | r i =>
    change radicalMap ((rotationAction^i.val) x) = rotation^i.val * radicalMap x * (rotation^i.val)⁻¹
    exact radicalMap_rotation_pow _ _
  | sr i =>
    change radicalMap (secondWeyl ((rotationAction^i.val) x)) =
      (reflection*rotation^i.val) * radicalMap x * (reflection*rotation^i.val)⁻¹
    rw [radicalMap_secondWeyl, radicalMap_rotation_pow]
    group

abbrev SecondModel := radical ⋊[secondAction] DihedralGroup 3

noncomputable def secondMap : SecondModel →* Endpoint :=
  SemidirectProduct.lift radicalMap secondSection (by
    intro g
    apply MonoidHom.ext
    intro x
    exact secondAction_compatible g x)

end Tits.AmalgamRigidity.FullRee.PointedPairs

namespace Tits.AmalgamRigidity.FullRee.PointedPairs
open ReeTwo SecondExtension Theory.GroupTheory

theorem secondMap_inl (x : radical) : secondMap (SemidirectProduct.inl x) = radicalMap x :=
  SemidirectProduct.lift_inl _ _ _ x

theorem secondMap_inr (x : DihedralGroup 3) : secondMap (SemidirectProduct.inr x) = secondSection x :=
  SemidirectProduct.lift_inr _ _ _ x

@[simp] theorem secondMap_reflection : secondMap (SemidirectProduct.inr (DihedralGroup.sr 0)) = reflection := by
  rw [secondMap_inr]
  change reflection * rotation^0 = reflection
  simp

theorem secondSection_firstRoot : secondSection (DihedralGroup.sr 2) = inclusion (SylowModel.root 0) := by
  change reflection * rotation^2 = inclusion (SylowModel.root 0)
  have hd : rotation^3=1 := weyl_relations.cube
  have hi : rotation^2=rotation⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using hd
  have hr : reflection * reflection = 1 := by simpa only [pow_two] using weyl_relations.square
  have hx : (inclusion (SylowModel.root 0))⁻¹ = inclusion (SylowModel.root 0) := by
    rw [← map_inv]
    exact congrArg inclusion (by decide +kernel : (SylowModel.root 0)⁻¹ = SylowModel.root 0)
  rw [hi, rotation, mul_inv_rev, hx, ← mul_assoc, mul_inv_cancel, one_mul]

theorem secondMap_surjective : Function.Surjective secondMap := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← endpoint_generated]
  apply (Subgroup.closure_le _).mpr
  rintro _ (rfl | ⟨x,rfl⟩)
  · exact ⟨SemidirectProduct.inr (DihedralGroup.sr 0), secondMap_reflection⟩
  · obtain ⟨k,i,he⟩ := sylow_split x
    refine ⟨SemidirectProduct.inl k * SemidirectProduct.inr (DihedralGroup.sr 2)^i.val, ?_⟩
    rw [map_mul, map_pow, secondMap_inl, secondMap_inr]
    change inclusion k.val * (secondSection (DihedralGroup.sr 2))^i.val = inclusion x
    rw [secondSection_firstRoot, ← map_pow, ← map_mul, he]

instance : Finite SecondModel :=
  Finite.of_equiv (radical × DihedralGroup 3) SemidirectProduct.equivProd.symm

theorem secondMap_bijective : Function.Bijective secondMap := by
  apply secondMap_surjective.bijective_of_nat_card_le
  rw [SemidirectProduct.card, radical_card, DihedralGroup.nat_card]
  change 2048 * (2 * 3) ≤ Nat.card Tits.ExceptionalParabolics.FullRee.second
  rw [Tits.ExceptionalParabolics.FullRee.second_card]

noncomputable def secondEquiv : SecondModel ≃* Endpoint :=
  MulEquiv.ofBijective secondMap secondMap_bijective

end Tits.AmalgamRigidity.FullRee.PointedPairs
