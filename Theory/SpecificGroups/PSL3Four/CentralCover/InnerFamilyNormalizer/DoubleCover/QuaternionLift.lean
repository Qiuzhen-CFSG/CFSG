module
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.Centerless.Order

/-!
# Lifting the concrete quaternion supplement through a double cover

The inverse image of the displayed Q₈ is a two-group when the covering
kernel is a two-group. Together with any subgroup mapping onto the marked
E₉, it generates the full inverse image of the graph-field fixed subgroup.
The displacement kills E₉, so all its values already occur above Q₈.
Involution lifting, through the proved Sylow-transfer calculation, makes
this restricted displacement surjective for a center-C₂ perfect cover.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.2.2(3b), printed pp.409–410, and 16.4.9(2), printed p.1191.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover
open ExtendedCentralizer.ProjectiveFixer
variable {H : Type*} [Group H]
variable (c : PerfectCentralCovering.Cover H PSL)

/-- The full inverse image of the concrete quaternion subgroup. -/
def quaternionPreimage : Subgroup H := Centerless.quaternion.comap c.toMonoidHom

theorem quaternionPreimage_le_fixed : quaternionPreimage c ≤ fixedPreimage c :=
  comap_mono Centerless.quaternion_le_fixed

/-- The original covering map restricted to the quaternion inverse image. -/
def quaternionProjection : quaternionPreimage c →* Centerless.quaternion :=
  c.toMonoidHom.restrict (fun _ hx => hx)

theorem quaternionProjection_surjective : Function.Surjective (quaternionProjection c) := by
  intro y
  obtain ⟨x, hx⟩ := c.surjective y
  exact ⟨⟨x, show c.toMonoidHom x ∈ Centerless.quaternion from hx ▸ y.property⟩, Subtype.ext hx⟩

theorem quaternionPreimage_two (hp : IsPGroup 2 c.toMonoidHom.ker) :
    IsPGroup 2 (quaternionPreimage c) :=
  Centerless.quaternion_isTwoGroup.comap_of_ker_isPGroup c.toMonoidHom hp

/-- A marked residual image and the full quaternion inverse image generate the
preimage of the projective fixed subgroup. -/
theorem fixedPreimage_eq_sup (D : Subgroup H)
    (hD : D.map c.toMonoidHom = model) :
    fixedPreimage c = D ⊔ quaternionPreimage c := by
  have hm : (D ⊔ quaternionPreimage c).map c.toMonoidHom = graphField.fixedSubgroup := by
    rw [Subgroup.map_sup, hD]
    change model ⊔ (Centerless.quaternion.comap c.toMonoidHom).map c.toMonoidHom = _
    rw [map_comap_eq_self_of_surjective c.surjective]
    exact Centerless.fixed_eq_model_sup_quaternion.symm
  rw [fixedPreimage, ← hm, comap_map_eq]
  exact sup_eq_left.mpr ((ker_le_comap c.toMonoidHom Centerless.quaternion).trans le_sup_right)

variable (a : MulAut H)
variable (ha : ∀ x, c.toMonoidHom (a x) = graphField (c.toMonoidHom x))
variable (hk : c.toMonoidHom.ker = center H) (hZ : Nat.card (center H) = 2)

/-- The descended displacement on the concrete quaternion supplement. -/
def quaternionCharacter : Centerless.quaternion →* center H :=
  (projectiveDisplacement c a ha hk hZ).comp (inclusion Centerless.quaternion_le_fixed)

theorem quaternionCharacter_apply (x : quaternionPreimage c) :
    quaternionCharacter c a ha hk hZ (quaternionProjection c x) =
      displacement c a ha (inclusion (quaternionPreimage_le_fixed c) x) := by
  exact projectiveDisplacement_apply c a ha hk hZ (inclusion (quaternionPreimage_le_fixed c) x)

/-- Since the displacement kills E₉, its image is already attained on Q₈. -/
theorem quaternionCharacter_surjective_of_surjective
    (hs : Function.Surjective (projectiveDisplacement c a ha hk hZ)) :
    Function.Surjective (quaternionCharacter c a ha hk hZ) := by
  let F := graphField.fixedSubgroup
  let f := projectiveDisplacement c a ha hk hZ
  have ht : model.subgroupOf F ⊔ Centerless.quaternion.subgroupOf F = ⊤ := by
    apply Subgroup.map_injective F.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le graphField_fixes_model,
      map_subgroupOf_eq_of_le Centerless.quaternion_le_fixed, ← MonoidHom.range_eq_map, range_subtype]
    exact Centerless.fixed_eq_model_sup_quaternion.symm
  have hm : (model.subgroupOf F).map f = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    change f x = 1
    exact projectiveDisplacement_model c a ha hk hZ ⟨x, hx⟩

  have hb : (Centerless.quaternion.subgroupOf F).map f = ⊤ := by
    have hf : (⊤ : Subgroup F).map f = ⊤ := by
      rw [← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr hs
    rw [← ht, Subgroup.map_sup, hm, bot_sup_eq] at hf
    exact hf
  intro y
  obtain ⟨x, hx, hxy⟩ := (show y ∈ (Centerless.quaternion.subgroupOf F).map f by
    rw [hb]; exact mem_top y)
  exact ⟨⟨x, hx⟩, hxy⟩

/-- I.2.2(3b) makes the quaternion character surjective. -/
theorem quaternionCharacter_surjective [Finite H] (ha2 : a ^ 2 = 1)
    (hlift : NontrivialDisplacement.InvolutionLifting c) :
    Function.Surjective (quaternionCharacter c a ha hk hZ) :=
  quaternionCharacter_surjective_of_surjective c a ha hk hZ
    (NontrivialDisplacement.projectiveDisplacement_surjective c a ha ha2 hk hZ hlift)

include hk hZ in
/-- Every central displacement is attained by an element above Q₈. -/
theorem quaternion_displacement_surjective [Finite H] (ha2 : a ^ 2 = 1)
    (hlift : NontrivialDisplacement.InvolutionLifting c) :
    Function.Surjective ((displacement c a ha).comp
      (inclusion (quaternionPreimage_le_fixed c))) := by
  intro y
  obtain ⟨b, hb⟩ := quaternionCharacter_surjective c a ha hk hZ ha2 hlift y
  obtain ⟨x, rfl⟩ := quaternionProjection_surjective c b
  exact ⟨x, (quaternionCharacter_apply c a ha hk hZ x).symm.trans hb⟩

end Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover
