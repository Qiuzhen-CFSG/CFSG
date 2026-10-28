module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Plane
/-!
# Marked actors in a literal Hermitian tensor overgroup

The marking identifies the intersection of a Sylow subgroup with the actual
inner image as the image of the full unitriangular group. Elementary actors
in this intersection lie in one of the two literal root planes: square-one
unitriangular matrices have one off-diagonal coordinate zero, and closure
under products makes that choice uniform. The faithful image has two-rank
4n, supplying the common rank bound.

Both radical maps are compared with the exact Chapter H image maps. The
inner subgroup is the actual solvable residual, with relative normality
in the given overgroup. Existence of a marked Sylow is a separate obligation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.4,
printed pp.455–456/PDF pp.466–467, and the H.4.2 flag on printed p.380.
-/

@[expose] public section
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.BinaryOffender
open Matrix.PSL3Even.UnipotentGeometry
open scoped ENNReal
noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Tensor
variable (n : ℕ) [NeZero n]
variable (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)

/-- The actual faithful inner image, as a subgroup of the source overgroup. -/
def innerActor : Subgroup M := (binaryImage n).comap M.subtype

/-- The full marked unitriangular subgroup, with both root planes retained. -/
def unipotentActor : Subgroup M := (unipotentToOvergroup n M hM).range

/-- The marking identifies the intersection with the inner image, not the
whole Sylow, which can contain outer field automorphisms. -/
def IsMarkedSylow (T : Sylow 2 M) : Prop :=
  (T : Subgroup M) ⊓ innerActor n M = unipotentActor n M hM

theorem elementary_le_radical (A : Subgroup M) (hA : IsElementaryTwo A)
    (hAU : A ≤ unipotentActor n M hM) :
    A ≤ pointActor n M hM ∨ A ≤ planeActor n M hM := by
  let f := unipotentToOvergroup n M hM
  let _ : IsElementaryAbelian 2 A := hA.2
  have hp : A.comap f ≤ V₁ (E n) ∨ A.comap f ≤ V₂ (E n) := by
    apply le_plane_of_exponent_two
    intro u hu
    apply unipotentToOvergroup_injective n M hM
    change f (u ^ 2) = f 1
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (f u) hu
  have hmap : (A.comap f).map f = A := Subgroup.map_comap_eq_self hAU
  rw [pointActor_eq_map, planeActor_eq_map]
  rcases hp with hp | hp
  · exact Or.inl (hmap ▸ Subgroup.map_mono hp)
  · exact Or.inr (hmap ▸ Subgroup.map_mono hp)

include hM in
theorem elementary_rank_le (A : Subgroup M) (hA : IsElementaryTwo A) : rank A ≤ 4 * n := by
  have hc := (primeRank_le_iff_elementary_card_le M).mp
    (CFSG.Quasithin.ChapterH.Section01To04.HermitianTensor.ImageOuter.source_twoRank_le n M hM)
    A hA.2
  rw [hA.card_eq_two_pow_rank] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

include hM in
theorem innerActor_eq_residual : innerActor n M = Subgroup.solvableResidual M := by
  ext g
  constructor
  · intro hg
    change g.val ∈ binaryImage n at hg
    rw [← hM] at hg
    obtain ⟨a,ha,hag⟩ := hg
    have he : a = g := Subtype.ext hag
    exact he ▸ ha
  · intro hg
    change g.val ∈ binaryImage n
    rw [← hM]
    exact ⟨g,hg,rfl⟩

theorem unipotentActor_le_inner : unipotentActor n M hM ≤ innerActor n M := by
  rintro g ⟨u,rfl⟩
  exact ⟨specialLinear (E n) u,rfl⟩

theorem planeActor_le_unipotent : planeActor n M hM ≤ unipotentActor n M hM := by
  rw [planeActor_eq_map]
  rintro g ⟨u,_,rfl⟩
  exact ⟨u,rfl⟩

theorem pointActor_le_unipotent : pointActor n M hM ≤ unipotentActor n M hM := by
  rw [pointActor_eq_map]
  rintro g ⟨u,_,rfl⟩
  exact ⟨u,rfl⟩

theorem planeActor_le_markedSylow (T : Sylow 2 M) (hT : IsMarkedSylow n M hM T) :
    planeActor n M hM ≤ T := by
  have hU : unipotentActor n M hM ≤ (T : Subgroup M) := by rw [← hT]; exact inf_le_left
  exact (planeActor_le_unipotent n M hM).trans hU

/-- Compatibility with the literal Chapter H plane subgroup and binary image map. -/
theorem planeActor_map_subtype : (planeActor n M hM).map M.subtype =
    (planeRadical n).map ((binaryImage n).subtype.comp (imageToBinaryImage n)) := by
  rw [planeActor, planeRadical, Subgroup.map_map, Subgroup.map_map]
  rfl

/-- Compatibility also retains the point-radical alternative. -/
theorem pointActor_map_subtype : (pointActor n M hM).map M.subtype =
    (pointRadical n).map ((binaryImage n).subtype.comp (imageToBinaryImage n)) := by
  rw [pointActor, pointRadical, Subgroup.map_map, Subgroup.map_map]
  rfl

end CFSG.Quasithin.ChapterK.Linear.Tensor
