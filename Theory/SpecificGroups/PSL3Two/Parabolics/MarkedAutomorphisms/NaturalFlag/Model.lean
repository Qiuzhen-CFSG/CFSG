module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The natural binary three-space and its marked automorphism action

The multiplicative form of the binary three-space has its actual coordinate
point and plane. The determinant-one matrix action identifies its full
automorphism group, and the stabilizers pull back to the literal matrix
parabolics. No abstract group identification is substituted for the action.

Source: Aschbacher--Smith, Notation 12.8.2 and 14.4.8(1), pp.849,1009.
-/

@[expose] public section

open Matrix Subgroup
open scoped Pointwise
namespace Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
abbrev Model := Multiplicative Fano.Vector

def point : Subgroup Model where
  carrier := {v | v.toAdd 1 = 0 ∧ v.toAdd 2 = 0}
  one_mem' := by simp
  mul_mem' := by rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩; exact ⟨by simp [ha, hb], by simp [ha', hb']⟩
  inv_mem' := by rintro a ⟨ha, ha'⟩; exact ⟨by simp [ha], by simp [ha']⟩
def plane : Subgroup Model where
  carrier := {v | v.toAdd 2 = 0}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb; simp_all
  inv_mem' := by intro a ha; simp_all

noncomputable def linearAut : (Fano.Vector ≃ₗ[ZMod 2] Fano.Vector) ≃* MulAut Model where
  toFun a := a.toAddEquiv.toMultiplicative
  invFun a := { AddEquiv.toMultiplicative.symm a with
    map_smul' := ZMod.map_smul (AddEquiv.toMultiplicative.symm a) }
  left_inv a := by ext; rfl
  right_inv a := by ext; rfl
  map_mul' a b := by ext; rfl
noncomputable def slAut : SL ≃* MulAut Model := equivGL.trans
  (GeneralLinearGroup.toLin.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Fano.Vector).trans linearAut))

theorem slAut_apply (g : SL) (v : Model) :
    (slAut g v).toAdd = g.val.mulVec v.toAdd := by
  rw [slAut, MulEquiv.trans_apply, equivGL_apply]
  rfl

theorem stabilizer_iff {E : Type*} [Group E] (P : Subgroup E) (g : MulAut E) :
    g ∈ MulAction.stabilizer (MulAut E) P ↔ ∀ x, g x ∈ P ↔ x ∈ P := by
  change P.map g.toMonoidHom = P ↔ _
  constructor
  · intro h x
    have hh := Subgroup.mem_map_iff_mem (f := g.toMonoidHom) (K := P) (x := x) g.injective
    simpa only [h, MulEquiv.coe_toMonoidHom] using hh
  · intro h
    ext x
    obtain ⟨x, rfl⟩ := g.surjective x
    simp only [Subgroup.mem_map_equiv, g.symm_apply_apply, h]

theorem point_stabilizer :
    (MulAction.stabilizer (MulAut Model) point).comap slAut.toMonoidHom = pointParabolicSL := by
  ext g
  rw [Subgroup.mem_comap, stabilizer_iff, pointParabolicSL, MulAction.mem_stabilizer_set]
  change (∀ x : Model, (slAut g x).toAdd 1 = 0 ∧ (slAut g x).toAdd 2 = 0 ↔
    x.toAdd 1 = 0 ∧ x.toAdd 2 = 0) ↔ _
  simp only [slAut_apply]
  rfl

theorem plane_stabilizer :
    (MulAction.stabilizer (MulAut Model) plane).comap slAut.toMonoidHom = lineParabolicSL := by
  ext g
  rw [Subgroup.mem_comap, stabilizer_iff, lineParabolicSL, MulAction.mem_stabilizer_set]
  change (∀ x : Model, (slAut g x).toAdd 2 = 0 ↔ x.toAdd 2 = 0) ↔ _
  simp only [slAut_apply]
  rfl


instance : DecidablePred (· ∈ point) := fun v =>
  inferInstanceAs (Decidable (v.toAdd 1 = 0 ∧ v.toAdd 2 = 0))
instance : DecidablePred (· ∈ plane) := fun v =>
  inferInstanceAs (Decidable (v.toAdd 2 = 0))


theorem card_point : Nat.card point = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel


theorem card_plane : Nat.card plane = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel


end Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
