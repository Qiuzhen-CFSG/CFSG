module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.Action
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.Centralizer
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Data.ZMod.Basic

/-!
# The actual overlap in the seventeen-point model amalgam

The point-pair intersection is the group of diagonal matrices together with
fourth-power Frobenius. Torus coordinates identify it with GF(16)ˣ extended
by that field involution. A cyclic marking of the units splits the order
fifteen torus into its cubic and quintic factors: Frobenius fixes the first
and inverts the second. The resulting actual subgroup is 3 × D₁₀.

Only the order-thirty coordinate group is checked by finite reduction. The
map into the genuine projective matrix extension, its image, and its
injectivity are proved structurally.

Source: Baumeister, *A geometry for groups of J₃-type* (2007), p.498,
the model amalgam preceding Corollary 2.10.
-/

@[expose] public section
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
namespace CyclicCoordinates
abbrev Fifteen := Multiplicative (ZMod 15)
abbrev Two := Multiplicative (ZMod 2)

def powerFour : MulAut Fifteen where
  toFun x := x ^ 4
  invFun x := x ^ 4
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

def action : Two →* MulAut Fifteen where
  toFun a := if a = 1 then 1 else powerFour
  map_one' := by simp
  map_mul' a b := by
    apply DFunLike.ext
    intro x
    revert a b x
    decide +kernel

abbrev AffineTorus := Fifteen ⋊[action] Two

instance : Fintype AffineTorus := Fintype.ofEquiv (Fifteen × Two) SemidirectProduct.equivProd.symm

def complementMap (x : AffineTorus) : Multiplicative (ZMod 3) × DihedralGroup 5 :=
  (Multiplicative.ofAdd (x.left.toAdd.val : ZMod 3),
    if x.right = 1 then DihedralGroup.r (x.left.toAdd.val : ZMod 5)
    else DihedralGroup.sr (-(x.left.toAdd.val : ZMod 5)))

def complementHom : AffineTorus →* (Multiplicative (ZMod 3) × DihedralGroup 5) where
  toFun := complementMap
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

noncomputable def complementEquiv : AffineTorus ≃* (Multiplicative (ZMod 3) × DihedralGroup 5) :=
  MulEquiv.ofBijective complementHom (by decide +kernel)

end CyclicCoordinates
end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam

@[expose] public noncomputable section
open Subgroup MulAction Matrix
open BenderSuzuki.Converse Theory.PSL2 Theory.PSL2.BinaryFourFieldExtension
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam

def torusHom : Fˣ →* BinaryGroup 4 := (quotientMap F).comp (BenderSuzuki.Converse.torHom F)

theorem torusHom_injective : Function.Injective torusHom :=
  (quotientMap_injective F).comp torHom_injective

theorem torus_range : torusHom.range = PTorus F := by
  rw [torusHom, MonoidHom.range_comp, ← Torus_eq_range]
  rfl

def unitsAction : Actor →* MulAut Fˣ where
  toFun a := Units.mapEquiv a.val.toMulEquiv
  map_one' := by ext u; rfl
  map_mul' a b := by ext u; rfl

theorem field_torus (a : Actor) (u : Fˣ) :
    action a (torusHom u) = torusHom (unitsAction a u) := by
  change fieldAut a.val (quotientMap F (tor u)) = quotientMap F (tor _)
  rw [fieldAut_apply_quotientMap]
  apply congrArg (quotientMap F)
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, tor_val, unitsAction,
      Units.coe_mapEquiv]

def torusLift : Fˣ ⋊[unitsAction] Actor →* Model :=
  SemidirectProduct.map torusHom (MonoidHom.id Actor) (by
    intro a
    apply MonoidHom.ext
    intro u
    exact (field_torus a u).symm)

theorem torusLift_injective : Function.Injective torusLift := by
  intro x y h
  apply SemidirectProduct.ext
  · exact torusHom_injective (congrArg SemidirectProduct.left h)
  · exact congrArg (fun z : Model => z.right) h

theorem torusLift_range : torusLift.range = point ⊓ pair := by
  ext x
  rw [mem_overlap]
  constructor
  · rintro ⟨y, rfl⟩
    exact torus_range ▸ (show torusHom y.left ∈ torusHom.range from ⟨y.left, rfl⟩)
  · intro hx
    obtain ⟨u, hu⟩ := torus_range.symm ▸ hx
    exact ⟨⟨u, x.right⟩, SemidirectProduct.ext hu rfl⟩

def torusLiftEquiv : Fˣ ⋊[unitsAction] Actor ≃* (point ⊓ pair : Subgroup Model) :=
  (MonoidHom.ofInjective torusLift_injective).trans (MulEquiv.subgroupCongr torusLift_range)

def unitsEquiv : Fˣ ≃* CyclicCoordinates.Fifteen := mulEquivOfCyclicCardEq (by
  rw [Nat.card_units, field_card]
  norm_num [CyclicCoordinates.Fifteen, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative])

theorem actor_eq_one_or_generator (a : Actor) : a = 1 ∨ a = actorGenerator := by
  have hc : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide +kernel
  rcases hc (actorEquiv a) with h | h
  · exact Or.inl (actorEquiv.injective (h.trans actorEquiv.map_one.symm))
  · exact Or.inr (actorEquiv.injective (h.trans actorEquiv_generator.symm))

theorem unitsAction_generator (u : Fˣ) : unitsAction actorGenerator u = u ^ 4 := by
  apply Units.ext
  exact fieldInvolution_apply u

def torusCoordinates : Fˣ ⋊[unitsAction] Actor ≃* CyclicCoordinates.AffineTorus :=
  SemidirectProduct.congr unitsEquiv actorEquiv (by
    intro a
    apply DFunLike.ext
    intro u
    rcases actor_eq_one_or_generator a with rfl | rfl
    · simp only [map_one, MulEquiv.trans_apply, MulAut.one_apply]
    · simp only [MulEquiv.trans_apply, actorEquiv_generator, unitsAction_generator, map_pow]
      rfl)

/-- The literal overlap, with its fourth-power field actor, has the source type. -/
def overlapEquiv : (point ⊓ pair : Subgroup Model) ≃*
    (Multiplicative (ZMod 3) × DihedralGroup 5) :=
  torusLiftEquiv.symm.trans (torusCoordinates.trans CyclicCoordinates.complementEquiv)

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
