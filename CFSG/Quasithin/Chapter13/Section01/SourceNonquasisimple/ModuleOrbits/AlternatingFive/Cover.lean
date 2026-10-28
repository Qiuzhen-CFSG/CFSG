module

public import CFSG.Quasithin.ChapterI.Section02.ModuleCovers.LinearTwo
public import Theory.Representation.FirstCohomologyDuality.Indecomposable
public import Theory.Representation.CentralCoverOriginalAction
public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.Representation.SL2NaturalFixedLifting.PointSylow

/-!
# The natural A₅ cover with its original normalizing actors

A fully moved central cover of the binary natural SL₂(4) module is a quotient
of the explicit orthogonal six-space. Twisted uniqueness makes the comparison
map equivariant for every original actor, even when that actor moves the
central kernel. Fixed-point lifting identifies each component stabilizer with
the stabilizer of the literal natural image and supplies a Sylow two-subgroup.

These are the covering and component-stabilizer inputs to the reducible branch
of Aschbacher--Smith 13.1.12, printed p.872, using I.1.5 and I.2.3. Orbit
lengths and the action of outer actors are separate obligations.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
open Representation Representation.OneCohomology
open Representation.OneCohomology.CentralCoverOriginalAction
open Representation.SL2FourNatural

abbrev Natural : Representation (ZMod 2) SL V :=
  SL2OrthogonalCover.binaryNatural
abbrev CoverSpace := SL2OrthogonalCover.Space F
abbrev CoverAction : Representation (ZMod 2) SL CoverSpace :=
  SL2OrthogonalCover.binaryAction
abbrev CoverProjection : CoverAction.IntertwiningMap Natural :=
  SL2OrthogonalCover.binaryProjection

private theorem field_card : Nat.card F = 2 ^ 2 := by
  rw [Nat.card_eq_fintype_card, card_field]
  rfl

private theorem field_large : 2 < Nat.card F := by rw [field_card]; decide

/-- The data of the original action and natural quotient. The fixed kernel
is required only for SL₂(4), not for the full actor A. -/
structure NaturalCover (A W : Type*) [Group A] [AddCommGroup W] [Module (ZMod 2) W] where
  component : Representation (ZMod 2) SL W
  actor : Representation (ZMod 2) A W
  conjugation : A →* MulAut SL
  naturalActor : Representation (ZMod 2) A V
  projection : component.IntertwiningMap Natural
  cover : IsCover projection
  compatible : ∀ a l w, actor a (component l w) = component (conjugation a l) (actor a w)
  quotient_action : ∀ a w, projection (actor a w) = naturalActor a (projection w)

namespace NaturalCover
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  (d : NaturalCover A W)

/-- Compatibility on the natural quotient follows from the original action. -/
theorem natural_compatible (a : A) (l : SL) (v : V) :
    d.naturalActor a (Natural l v) = Natural (d.conjugation a l) (d.naturalActor a v) := by
  obtain ⟨w,rfl⟩ := d.cover.1 v
  rw [← d.projection.isIntertwining, ← d.quotient_action, d.compatible,
    d.projection.isIntertwining, d.quotient_action]

/-- The central kernel is exactly the component-fixed space. -/
theorem fixed_eq_kernel : fixed d.component = d.projection.toLinearMap.ker := by
  apply le_antisymm _ d.cover.2.1
  intro w hw
  have hn : d.projection w ∈ fixed Natural := by
    intro l
    rw [← d.projection.isIntertwining, hw l]
  change d.projection w = 0
  simpa only [SL2OrthogonalCover.natural_fixed, Submodule.mem_bot] using hn

/-- The original kernel has binary dimension at most two. -/
theorem kernel_finrank_le_two [FiniteDimensional (ZMod 2) W] :
    Module.finrank (ZMod 2) d.projection.toLinearMap.ker ≤ 2 := by
  have h := finrank_ker_le_H1_of_cover d.projection d.cover
  rw [SL2OrthogonalCover.binary_dual_H1_finrank 2 (by decide) field_card] at h
  exact h

/-- A two-dimensional central kernel forces the full six-dimensional cover. -/
theorem finrank_eq_six_of_kernel [FiniteDimensional (ZMod 2) W]
    (h : Module.finrank (ZMod 2) d.projection.toLinearMap.ker = 2) :
    Module.finrank (ZMod 2) W = 6 := by
  have hd := d.projection.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr d.cover.1, finrank_top, finrank_vector, h] at hd
  exact hd.symm

/-- The orthogonal model maps onto the original cover, over the literal
natural projection and equivariantly for every original actor. -/
theorem exists_original_orthogonal_cover [FiniteDimensional (ZMod 2) W] :
    ∃ (ζ : Representation (ZMod 2) A CoverSpace)
      (f : CoverAction.IntertwiningMap d.component),
      Function.Surjective f ∧
      (∀ a l u, ζ a (CoverAction l u) = CoverAction (d.conjugation a l) (ζ a u)) ∧
      (∀ a u, CoverProjection (ζ a u) = d.naturalActor a (CoverProjection u)) ∧
      (∀ u, d.projection (f u) = CoverProjection u) ∧
      (∀ a u, f (ζ a u) = d.actor a (f u)) := by
  have hp : IsCover CoverProjection := SL2OrthogonalCover.binaryProjection_isCover field_large
  have hd : Module.finrank (ZMod 2) CoverProjection.toLinearMap.ker =
      Module.finrank (ZMod 2) (H1 Natural.dual) := by
    rw [SL2OrthogonalCover.binary_kernel_finrank 2 field_card,
      SL2OrthogonalCover.binary_dual_H1_finrank 2 (by decide) field_card]
  obtain ⟨ζ,hζ,hq,_⟩ := exists_action CoverProjection hp hd
    d.conjugation d.naturalActor d.natural_compatible
  obtain ⟨f,hf,hover⟩ := exists_quotient_of_finrank_ker_eq CoverProjection hp hd
    d.projection d.cover
  refine ⟨ζ,f,hf,hζ,hq,hover,?_⟩
  intro a u
  have he : f.toLinearMap.comp (ζ a) = (d.actor a).comp f.toLinearMap := by
    apply lift_unique CoverAction (d.component.comp (d.conjugation a).toMonoidHom)
      hp.2.2 d.projection.toLinearMap (fun w hw l => d.cover.2.1 hw (d.conjugation a l))
    · intro l w
      change f (ζ a (CoverAction l w)) = d.component (d.conjugation a l) (f (ζ a w))
      rw [hζ, f.isIntertwining]
    · intro l w
      change d.actor a (f (CoverAction l w)) =
        d.component (d.conjugation a l) (d.actor a (f w))
      rw [f.isIntertwining, d.compatible]
    · intro w
      change d.projection (f (ζ a w)) = d.projection (d.actor a (f w))
      rw [hover, hq, d.quotient_action, hover]
  exact LinearMap.congr_fun he u

/-- At central rank two the quotient comparison is an actual equivalence,
retaining both the natural projection and the original normalizing action. -/
theorem exists_original_orthogonal_equiv [FiniteDimensional (ZMod 2) W]
    (hk : Module.finrank (ZMod 2) d.projection.toLinearMap.ker = 2) :
    ∃ (ζ : Representation (ZMod 2) A CoverSpace) (e : CoverAction.Equiv d.component),
      (∀ a l u, ζ a (CoverAction l u) = CoverAction (d.conjugation a l) (ζ a u)) ∧
      (∀ a u, CoverProjection (ζ a u) = d.naturalActor a (CoverProjection u)) ∧
      (∀ u, d.projection (e u) = CoverProjection u) ∧
      (∀ a u, e (ζ a u) = d.actor a (e u)) := by
  obtain ⟨ζ,f,hf,hζ,hq,hover,hact⟩ := d.exists_original_orthogonal_cover
  have hd : Module.finrank (ZMod 2) CoverSpace = 6 := by
    have h := CoverProjection.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr
      (SL2OrthogonalCover.binaryProjection_isCover field_large).1, finrank_top,
      finrank_vector, SL2OrthogonalCover.binary_kernel_finrank 2 field_card] at h
    exact h.symm
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hd.trans (d.finrank_eq_six_of_kernel hk).symm)).mpr hf
  let e : CoverAction.Equiv d.component :=
    Representation.Equiv.mk (LinearEquiv.ofBijective f.toLinearMap ⟨hi,hf⟩) f.isIntertwining'
  exact ⟨ζ,e,hζ,hq,hover,hact⟩

/-- Central-cover fixed lifting retains the same component element. -/
theorem fixed_iff_natural_fixed (l : SL) (w : W) :
    d.component l w = w ↔ Natural l (d.projection w) = d.projection w := by
  constructor
  · intro h
    rw [← d.projection.isIntertwining, h]
  · intro h
    apply SL2NaturalFixedLifting.fixed_lift_of_fixed_kernel d.component
      d.projection.toLinearMap.toAddMonoidHom d.cover.1
      (fun g v => LinearMap.congr_fun (d.projection.isIntertwining' g) v)
      (fun _ hv g => d.cover.2.1 hv g) l w
    change d.projection (d.component l w) = d.projection w
    rw [d.projection.isIntertwining, h]

/-- Every vector has a full component Sylow in its actual stabilizer. -/
theorem exists_component_sylow_fixed (w : W) :
    ∃ S : Sylow 2 SL, ∀ l ∈ (S : Subgroup SL), d.component l w = w :=
  SL2NaturalFixedLifting.exists_sylow_fixed_of_fixed_kernel d.component
    d.projection.toLinearMap.toAddMonoidHom d.cover.1
    (fun l v => LinearMap.congr_fun (d.projection.isIntertwining' l) v)
    (fun _ hv l => d.cover.2.1 hv l) w

end NaturalCover
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
