module
public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Action

/-!
# The local octad action in the genuine triality quotient

The kernel of `n1ToC` kills the restricted short action. Consequently the
local representation descends to `N1/K`, and the established quotient
isomorphism transports it to `N1Image`, the actual subgroup of `N/K`.
The inclusion equation uses the existing embedding of that subgroup in C.
These are the literal barred actors for the subsequent relative-kernel
calculations; no group-family identification is involved.

Source: Aschbacher, *Sporadic Groups*, Section 27 and Lemma 29.13,
printed pp. 149 and 160–161.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure
open LocalC TrialitySpin

/-- The original central kernel is killed by the literal local action. -/
theorem representation_killed (g : N1) (hg : g.val ∈ K) : representation g = 1 := by
  have hc : n1ToC g = 1 := by
    change g ∈ n1ToC.ker
    rw [n1ToC_kernel]
    exact hg
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change cShort (n1ToC g) v.val = v.val
  rw [hc, map_one]
  rfl

theorem representation_kernel : K.subgroupOf N1 ≤ representation.ker :=
  fun g hg => representation_killed g hg

/-- The representation of the literal local quotient `N1/K`. -/
def localQuotientRepresentation : Representation ℝ N1Quotient Space :=
  QuotientGroup.lift (K.subgroupOf N1) representation representation_kernel

@[simp] theorem localQuotientRepresentation_mk (g : N1) :
    localQuotientRepresentation (QuotientGroup.mk' (K.subgroupOf N1) g) = representation g := rfl

/-- The same action on the actual image subgroup inside `N/K`. -/
def imageRepresentation : Representation ℝ N1Image Space :=
  localQuotientRepresentation.comp n1QuotientEquivImage.symm.toMonoidHom

@[simp] theorem imageRepresentation_map (g : N1) :
    imageRepresentation (n1ImageMap g) = representation g := by
  change localQuotientRepresentation (n1QuotientEquivImage.symm (n1ImageMap g)) = _
  rw [← n1QuotientEquivImage_mk, n1QuotientEquivImage.symm_apply_apply,
    localQuotientRepresentation_mk]

/-- The descended local action still intertwines the literal inclusion in `C`. -/
theorem imageRepresentation_inclusion (g : N1Image) (v : Space) :
    inclusion (imageRepresentation g v) =
      cRepresentation (n1ImageToC g) (inclusion v) := by
  obtain ⟨g, rfl⟩ := n1ImageMap_surjective g
  rw [imageRepresentation_map, n1ImageToC_map]
  exact representation_inclusion g v

/-- The original extension condition can equally be checked in the actual local image. -/
theorem extendsLocal_iff_image (ρ : Representation ℝ N Space) :
    ExtendsLocal ρ ↔ ∀ g : N1, ρ g.val = imageRepresentation (n1ImageMap g) := by
  simp only [imageRepresentation_map, extendsLocal_iff]

end Sporadic.Monster.Construction.NOctad.LocalStructure
