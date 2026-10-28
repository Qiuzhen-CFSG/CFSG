module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.PlaneAction.Natural
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.RadicalLifts

/-!
# Aligning the old symplectic module in the reverse triangle

Undo the common Sylow alignment simultaneously on the model group and its
natural module. Uniqueness identifies any original invariant field flag
with the canonical flag. The surjective residual projection then identifies
its literal second-residual image with the standard plane local subgroup.
The existing core calculation supplies representatives for its original
second radical. The paired G₂ flag must still be constructed separately.

Source: Aschbacher--Smith, 11.1.2(3), printed p.764, and 11.4.1(2), p.776.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- The group and module marking change by the same inverse Sylow alignment. -/
def alignedSymplecticMark : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)) where
  groupEquiv := m.groupEquiv.trans (MulAut.conj (LocalGeometry.Sp4.alignment m)⁻¹)
  linearEquiv := m.linearEquiv.trans
    ((toLinear (LocalGeometry.Sp4.alignment m)⁻¹).restrictScalars (ZMod 2))
  intertwines q v := by
    change (LocalGeometry.Sp4.alignment m)⁻¹ •
      m.linearEquiv (D.centralQuotientAction q v) =
      ((LocalGeometry.Sp4.alignment m)⁻¹ * m.groupEquiv q *
        ((LocalGeometry.Sp4.alignment m)⁻¹)⁻¹) •
          ((LocalGeometry.Sp4.alignment m)⁻¹ • m.linearEquiv v)
    rw [m.intertwines]
    change (LocalGeometry.Sp4.alignment m)⁻¹ •
      (m.groupEquiv q • m.linearEquiv v) = _
    simp only [mul_smul, inv_inv, smul_inv_smul]

/-- The original flag residual maps onto the standard plane residual;
no residual equality or image bound is an input. -/
theorem alignedSymplecticMark_plane_image
    (f : LocalGeometry.InvariantFlag (LocalGeometry.Coordinates.sp4 m)) :
    ((f.Li 1).subgroupOf L).map
      ((alignedSymplecticMark S m).groupEquiv.toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 L))) = planeLocal := by
  have hs : f.space 1 = (LocalGeometry.Sp4.flag m S).space 1 :=
    LocalGeometry.Sp4.flag_unique m S 1 (f.space 1) (f.dimension 1) (f.invariant 1)
  have hr : f.Li 1 = (LocalGeometry.Sp4.flag m S).Li 1 := by
    change LocalGeometry.localResidual L
      ((LocalGeometry.Coordinates.sp4 m).preimage (f.space 1)) = _
    rw [hs]
    rfl
  rw [hr]
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    let r : (LocalGeometry.Sp4.flag m S).Li 1 := ⟨l.val, hl⟩
    have hp := (LocalGeometry.Sp4.PlaneAction.localProjection S m 1 r).property
    change (LocalGeometry.Sp4.PlaneAction.localProjection S m 1 r).val ∈
      planeLocal at hp
    rw [LocalGeometry.Sp4.PlaneAction.localProjection_coe] at hp
    change (LocalGeometry.Sp4.alignment m)⁻¹ *
      m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) *
        ((LocalGeometry.Sp4.alignment m)⁻¹)⁻¹ ∈ planeLocal
    convert (show _ from hp) using 1
    simp only [LocalGeometry.Coordinates.quotientMap,
      LocalGeometry.Coordinates.groupEquiv, MonoidHom.comp_apply,
      r, inv_inv]
    rfl
  · intro hg
    obtain ⟨r, hr⟩ := LocalGeometry.Sp4.PlaneAction.localProjection_surjective S m 1 ⟨g, hg⟩
    refine ⟨⟨r.val, (LocalGeometry.localResidual_le _ r.property).1⟩, r.property, ?_⟩
    change (LocalGeometry.Sp4.alignment m)⁻¹ *
      m.groupEquiv (QuotientGroup.mk' (pCore 2 L)
        ⟨r.val, (LocalGeometry.localResidual_le _ r.property).1⟩) *
          ((LocalGeometry.Sp4.alignment m)⁻¹)⁻¹ = g
    convert (LocalGeometry.Sp4.PlaneAction.localProjection_coe S m 1 r).symm.trans
        (congrArg Subtype.val hr) using 1
    simp only [LocalGeometry.Coordinates.quotientMap,
        LocalGeometry.Coordinates.groupEquiv, MonoidHom.comp_apply,
        inv_inv]
    rfl

/-- The literal original second radical has the representatives needed when
the old symplectic module becomes the swapped module. -/
theorem alignedSymplecticMark_radical_lifts
    (f : LocalGeometry.InvariantFlag (LocalGeometry.Coordinates.sp4 m)) :
    HasPlaneRadicalLifts D (alignedSymplecticMark S m) (f.Ri 1) := by
  exact planeRadicalLifts_of_plane_residual D (alignedSymplecticMark S m) S.nonbinary
    (f.Li 1) ((LocalGeometry.localResidual_le _).trans inf_le_left)
    (f.sylow_normalizes_Li 1) (alignedSymplecticMark_plane_image S m f)

/-- Application retains the `ofFlag` geometry's actual R₂. -/
theorem ofFlag_alignedSymplecticMark_radical_lifts
    (f : LocalGeometry.InvariantFlag (LocalGeometry.Coordinates.sp4 m))
    (X : Subgroup G) (z : G) (H : Subgroup G) :
    HasPlaneRadicalLifts D (alignedSymplecticMark S m) (ofFlag S f X z H).R₂ :=
  alignedSymplecticMark_radical_lifts S m f

/-- Construct the action of the unchanged second radical on the old symplectic
module. The full preceding shadow implication supplies fixed-space vanishing;
no plane-placement or radical-representative premise remains. -/
theorem ofFlag_alignedSymplecticMark_action
    (f : LocalGeometry.InvariantFlag (LocalGeometry.Coordinates.sp4 m))
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (U₁ : Submodule (ZMod 2) D.chosenCentralQuotient)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ H₀, Hypothesis1131At D S U₁ H₀ → Proposition1132At D S U₁ H₀) :
    ∃ (e : V ≃* Multiplicative (Vector S.field.Carrier))
      (α : (ofFlag S f X z H).R₂ →* Sp S.field.Carrier),
      (∀ (a : (ofFlag S f X z H).R₂) (v : V),
        (e ⟨a.val * v.val * a.val⁻¹,
          (mem_normalizer_iff.mp
            (S.sylow_normalizes (LocalGeometry.localRadical_le_sylow _ a.property))
            v.val).mp v.property⟩).toAdd = α a • (e v).toAdd) ∧
      α.range ≤ Plane.radical.map planeLocal.subtype := by
  have hfix := fixed_trivial D S U₁ hlinear h1132
  obtain ⟨_, α, hα, himage⟩ := exists_plane_radical_action D hfix
    (alignedSymplecticMark S m) (ofFlag S f X z H).R₂
    (ofFlag_alignedSymplecticMark_radical_lifts S m f X z H)
  exact ⟨symplecticEquiv D hfix (alignedSymplecticMark S m), α, hα, himage⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
