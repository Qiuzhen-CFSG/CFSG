module

public import Theory.Representation.HermitianTensorThree.FieldInvolution
public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic

/-!
# The marked flag and its subgroups in the descended tensor image

The flag is the first coordinate line in the first coordinate plane.
Both parabolics are images of the literal natural-space stabilizers under
the descended action. The two root-plane subgroups are images of the usual
upper-unitriangular coordinates; their identification as the full unipotent
radicals is a separate theorem. These choices agree with H.4.2 on printed
p.380 of Aschbacher–Smith, combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace Representation.HermitianTensorThree
open Matrix.PSL3Even.UnipotentGeometry
variable (n : ℕ) [NeZero n]

/-- The marked line Z = E e₀ in the genuine natural module. -/
def flagLine : Submodule (E n) (Natural n) where
  carrier := {x | x 1 = 0 ∧ x 2 = 0}
  zero_mem' := ⟨rfl,rfl⟩
  add_mem' := by rintro x y ⟨h1,h2⟩ ⟨k1,k2⟩; exact ⟨by simp [h1,k1], by simp [h2,k2]⟩
  smul_mem' := by rintro c x ⟨h1,h2⟩; exact ⟨by simp [h1], by simp [h2]⟩

/-- The marked plane W = E e₀ + E e₁. -/
def flagPlane : Submodule (E n) (Natural n) := (LinearMap.proj (2 : Fin 3)).ker

omit [NeZero n] in
theorem flagLine_lt_flagPlane : flagLine n < flagPlane n := by
  refine lt_of_le_of_ne (fun x hx => hx.2) ?_
  intro he
  have h : (![0,1,0] : Natural n) ∈ flagPlane n := rfl
  rw [← he] at h
  exact one_ne_zero h.1

omit [NeZero n] in
theorem flagLine_ne_bot : flagLine n ≠ ⊥ := by
  intro he
  have h : (![1,0,0] : Natural n) ∈ flagLine n := ⟨rfl,rfl⟩
  rw [he, Submodule.mem_bot] at h
  exact one_ne_zero (congrFun h 0)

omit [NeZero n] in
theorem flagPlane_ne_top : flagPlane n ≠ ⊤ := by
  intro he
  have h : (![0,0,1] : Natural n) ∈ flagPlane n := he ▸ Submodule.mem_top
  exact one_ne_zero h

/-- Cover parabolics retain the exact natural flag stabilizers. -/
abbrev coverPointParabolic : Subgroup (Cover n) := Matrix.PSL3.LinearThree.pointParabolicSL (E n)
abbrev coverPlaneParabolic : Subgroup (Cover n) := Matrix.PSL3.LinearThree.lineParabolicSL (E n)

def pointParabolic : Subgroup (Image n) := (coverPointParabolic n).map (toImage n)
def planeParabolic : Subgroup (Image n) := (coverPlaneParabolic n).map (toImage n)

/-- The two root planes in the natural SL₃ cover. -/
def coverPointRadical : Subgroup (Cover n) :=
  (V₁ (E n)).map (specialLinear (E n))
def coverPlaneRadical : Subgroup (Cover n) :=
  (V₂ (E n)).map (specialLinear (E n))

def pointRadical : Subgroup (Image n) := (coverPointRadical n).map (toImage n)
def planeRadical : Subgroup (Image n) := (coverPlaneRadical n).map (toImage n)

omit [NeZero n] in
theorem coverPointRadical_le : coverPointRadical n ≤ coverPointParabolic n := by
  rintro g ⟨u,hu,rfl⟩
  rw [Matrix.PSL3.LinearThree.mem_pointParabolicSL_iff]
  exact ⟨rfl,rfl⟩

omit [NeZero n] in
theorem coverPlaneRadical_le : coverPlaneRadical n ≤ coverPlaneParabolic n := by
  rintro g ⟨u,hu,rfl⟩
  rw [Matrix.PSL3.LinearThree.mem_lineParabolicSL_iff]
  exact ⟨rfl,rfl⟩

theorem pointRadical_le : pointRadical n ≤ pointParabolic n :=
  Subgroup.map_mono (coverPointRadical_le n)

theorem planeRadical_le : planeRadical n ≤ planeParabolic n :=
  Subgroup.map_mono (coverPlaneRadical_le n)

/-- An arbitrary source overgroup keeps its literal faithful binary action. -/
def overgroupAction (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) :
    Representation (ZMod 2) M (Space n) where
  toFun g := g.val.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

theorem overgroupAction_faithful (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) :
    Function.Injective (overgroupAction n M) := by
  intro g h he
  apply Subtype.ext
  exact LinearEquiv.toLinearMap_injective he

end Representation.HermitianTensorThree
