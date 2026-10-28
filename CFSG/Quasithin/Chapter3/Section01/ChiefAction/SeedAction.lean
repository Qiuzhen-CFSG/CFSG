module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.Seed
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import Theory.Representation.BinaryOffender.IrreducibleResidual

/-!
# The faithful action of the source essential quotient

Keep the original invariant kernel W and original seed v in V. The essential
residual image in U/W is an actual irreducible subrepresentation. Its faithful
action image has trivial two-core. Its action kernel is proper because the
nonzero seed cannot be fixed by the entire residual in U/W. The reduced-image
theorem therefore makes the image a minimal parabolic over the mapped original
Sylow subgroup.

The source constructor proves every field of the package from the original
QRC, inside-core and ratio-two inputs. It returns the literal action homomorphism
and seed vector, including pointwise compatibility with all lifts centralizing
V. It introduces no natural-module or classification premise.

Source: Aschbacher–Smith, original3.1.9(5), printed p.578, used in15.1.12(3).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open Representation.EssentialResidualQuotient
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory ChapterB
variable {G : Type*} [Group G] (H V : Subgroup G)
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]

/-- The literal essential quotient and original seed, with the source geometry. -/
structure EssentialSeedAction (S : Sylow 2 H) (hVH : V ≤ H) where
  kernel : Subrepresentation (normalRepresentation ((conjugateSpan H V).subgroupOf H))
  seed : V
  avoids : ¬ moved (normalRepresentation ((conjugateSpan H V).subgroupOf H))
    (pResidual 2 H) ≤ kernel
  maximal : ∀ N, kernel < N →
    moved (normalRepresentation ((conjugateSpan H V).subgroupOf H)) (pResidual 2 H) ≤ N
  irreducible : IsIrreducible (kernel.quotientImage
    (moved (normalRepresentation ((conjugateSpan H V).subgroupOf H)) (pResidual 2 H))).toRepresentation
  essential : ∀ N : Subrepresentation kernel.quotientRepresentation, N ≠ ⊥ →
    kernel.quotientImage (moved (normalRepresentation ((conjugateSpan H V).subgroupOf H))
      (pResidual 2 H)) ≤ N
  residual_fixed : fixedSpace kernel.quotientRepresentation (pResidual 2 H) = ⊥
  seed_mem : kernel.toSubmodule.mkQ (spanSeedVector H V hVH seed) ∈
    kernel.quotientImage (moved (normalRepresentation ((conjugateSpan H V).subgroupOf H))
      (pResidual 2 H))
  seed_nonzero : kernel.toSubmodule.mkQ (spanSeedVector H V hVH seed) ≠ 0
  seed_sylow_fixed : kernel.toSubmodule.mkQ (spanSeedVector H V hVH seed) ∈
    fixedSpace kernel.quotientRepresentation S
  seed_centralizer_fixed : ∀ x : H, (x : G) ∈ centralizer (V : Set G) →
    kernel.quotientRepresentation x (kernel.toSubmodule.mkQ (spanSeedVector H V hVH seed)) =
      kernel.toSubmodule.mkQ (spanSeedVector H V hVH seed)
  original_minimal : IsMinimalParabolicOver S ⊤

namespace EssentialSeedAction
variable {H V} {S : Sylow 2 H} {hVH : V ≤ H}
  (a : EssentialSeedAction H V S hVH)

/-- The actual simple residual image in the quotient by W. -/
abbrev socle := a.kernel.quotientImage
  (moved (normalRepresentation ((conjugateSpan H V).subgroupOf H)) (pResidual 2 H))
/-- The original H action restricted to that image. -/
abbrev representation := a.socle.toRepresentation
/-- The faithful actor is the literal image of the restricted representation. -/
abbrev Actor := actionImage a.representation
/-- The original action homomorphism, corestricted to its image. -/
abbrev projection : H →* a.Actor := Representation.BinaryOffender.actionHom a.representation
/-- The tautological faithful action on the same essential subspace. -/
abbrev imageRepresentation := Representation.BinaryOffender.imageRepresentation a.representation
/-- The image of the original seed element, now in the essential subspace. -/
def vector : a.socle.toSubmodule :=
  ⟨a.kernel.toSubmodule.mkQ (spanSeedVector H V hVH a.seed),a.seed_mem⟩

/-- Corestriction to the actual action image is onto. -/
theorem projection_surjective : Function.Surjective a.projection :=
  a.representation.asGroupHom.rangeRestrict_surjective

/-- Passing to the essential subspace retains the nonzero source vector. -/
theorem vector_ne_zero : a.vector ≠ 0 := by
  intro hh
  exact a.seed_nonzero (congrArg Subtype.val hh)

/-- The faithful image of every original centralizing lift fixes this vector. -/
theorem vector_centralizer_fixed (x : H) (hx : (x : G) ∈ centralizer (V : Set G)) :
    a.imageRepresentation (a.projection x) a.vector = a.vector := by
  apply Subtype.ext
  exact a.seed_centralizer_fixed x hx

variable [Finite G]

/-- The mapped original Sylow subgroup fixes the same vector. -/
theorem vector_sylow_fixed : a.vector ∈ fixedSpace a.imageRepresentation
    ((S.mapSurjective a.projection_surjective : Sylow 2 a.Actor) : Subgroup a.Actor) := by
  rintro ⟨_,x,hx,rfl⟩
  apply Subtype.ext
  exact a.seed_sylow_fixed ⟨x,hx⟩

/-- Irreducibility makes the faithful action image reduced. -/
theorem twoCore_eq_bot : pCore 2 a.Actor = ⊥ := by
  let := a.irreducible
  exact irreducible_image_twoCore_eq_bot a.representation

omit [Finite G] in
/-- The source residual fixed-space vanishing makes the action nontrivial. -/
theorem projection_kernel_ne_top : a.projection.ker ≠ ⊤ := by
  intro hh
  have hfix : (a.vector : Additive ((conjugateSpan H V).subgroupOf H) ⧸ a.kernel.toSubmodule) ∈
      fixedSpace a.kernel.quotientRepresentation (pResidual 2 H) := by
    intro k
    have hk : a.projection (k : H) = 1 := by
      exact show (k : H) ∈ a.projection.ker from hh.symm ▸ mem_top _
    have hf := (Representation.BinaryOffender.actionHom_eq_one_iff a.representation (k : H)).mp hk a.vector
    exact congrArg Subtype.val hf
  rw [a.residual_fixed,Submodule.mem_bot] at hfix
  exact a.seed_nonzero hfix

/-- The faithful image is minimal parabolic over the mapped original Sylow. -/
theorem reduced_minimal : IsMinimalParabolicOver
    (S.mapSurjective a.projection_surjective) ⊤ :=
  (minimalParabolic_reduced_image S a.original_minimal a.projection
    a.projection_surjective a.twoCore_eq_bot a.projection_kernel_ne_top).2

end EssentialSeedAction
end CFSG.Quasithin.Chapter3

namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The original source constructs the actual essential action and original seed;
all faithful-image and minimal-parabolic properties are available as methods. -/
theorem QrcHypotheses.sqtk_essential_seed_action
    (h : QrcHypotheses T M M₀ H V)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2) :
    let d := h.toQRCConfiguration (h.no_common_normal hu)
    let U := (conjugateSpan H V).subgroupOf H
    letI := d.module_elementary
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    Nonempty (EssentialSeedAction H V (T.subtype h.right_mem.1.1.2)
      (hV.trans (twoCore_le H))) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let U := (conjugateSpan H V).subgroupOf H
  let S := T.subtype h.right_mem.1.1.2
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  have hS : (S : Subgroup H).map H.subtype = T :=
    map_subgroupOf_eq_of_le h.right_mem.1.1.2
  have hp := source_intrinsic_minimalParabolic_of_notFF d hne
    (source_notFF_of_ratio_two d hq) S hS
  obtain ⟨W,hW,hmax,hi,he,hfixed,v,hvn,hvS,hvs,hvc⟩ :=
    h.sqtk_essential_fixed_seed hu hne hV hq
  exact ⟨{
    kernel := W
    seed := v
    avoids := hW
    maximal := hmax
    irreducible := hi
    essential := he
    residual_fixed := hfixed
    seed_mem := hvs
    seed_nonzero := hvn
    seed_sylow_fixed := hvS
    seed_centralizer_fixed := hvc
    original_minimal := hp }⟩

end CFSG.Quasithin.Chapter3
