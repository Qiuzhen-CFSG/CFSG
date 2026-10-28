module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.UpperSection
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.ParabolicSection
public import Theory.Representation.SylowNormalizerIntertwiner
public import Theory.Representation.SL2FourNaturalOrbits.BorelDualCore
public import Theory.Representation.Quotient

/-!
# Aligning the actual natural marking with the Borel

Sylow conjugacy aligns c.model with the upper root, and the source root-normalizer
identity identifies the local image with the upper Borel. Acting on all natural
coordinates by the same conjugator preserves equivariance. The source's A5 and
SL2 markings are compared through their common starred quotient, never assumed
to agree. Source: Aschbacher--Smith 13.5.22(2), p.924/PDF p.941, using G.2.4.
-/

@[expose] public section
noncomputable section
open Subgroup NoncentralChiefRefinement Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.NaturalParabolic
open ChapterG.Section02 ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive
open ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

theorem exists_natural_alignment_conjugator
    {D : Setup G} {g : G} (d : Hypothesis D g)
    [((AlternatingFive.S₂ D g).subgroupOf (D.S g)).Normal]
    {s : ℕ} (c : NaturalLayer D g F4 s d.L_le_I) :
    ∃ a : SL(2, F4),
      ((D.star D.U).subgroupOf (D.star D.L)).map
          (c.model.trans (MulAut.conj a)).toMonoidHom =
        Matrix.SpecialLinearGroup.upperUnipotent F4 ∧
      ((D.star D.L₁).subgroupOf (D.star D.L)).map
          (c.model.trans (MulAut.conj a)).toMonoidHom =
        Matrix.SpecialLinearGroup.rankOneBorel F4 := by
  obtain ⟨P, hP⟩ := d.star_U_sylow
  have hP' : (P : Subgroup (D.star D.L)) =
      (D.star D.U).subgroupOf (D.star D.L) := by
    ext x
    constructor
    · intro hx
      change (x : D.Star) ∈ D.star D.U
      rw [← hP]
      exact ⟨x, hx, rfl⟩
    · intro hx
      change (x : D.Star) ∈ D.star D.U at hx
      rw [← hP] at hx
      obtain ⟨y, hy, he⟩ := hx
      exact (show y = x from Subtype.ext he) ▸ hy
  let R : Sylow 2 SL(2, F4) :=
    P.mapSurjective (f := c.model.toMonoidHom) c.model.surjective
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq SL(2, F4) R
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F4 2)
  have h := congrArg (fun Q : Sylow 2 SL(2, F4) =>
      (Q : Subgroup SL(2, F4))) ha
  change ((P : Subgroup (D.star D.L)).map c.model.toMonoidHom).map
    (MulAut.conj a).toMonoidHom = Matrix.SpecialLinearGroup.upperUnipotent F4 at h
  rw [hP', Subgroup.map_map] at h
  refine ⟨a, h, ?_⟩
  rw [d.star_local_eq_root_normalizer,
    Subgroup.map_equiv_normalizer_eq]
  change Subgroup.normalizer (Subgroup.map
      ((MulAut.conj a).toMonoidHom.comp c.model.toMonoidHom)
      ((D.star D.U).subgroupOf (D.star D.L)) : Set (SL(2, F4))) = _
  rw [h]

/-! The model conjugator acts on every copy of the coordinate plane. -/

noncomputable def adjustedAddEquiv {s : ℕ} (a : SL(2, F4)) :
    (Fin s → Fin 2 → F4) ≃ₗ[ZMod 2] (Fin s → Fin 2 → F4) :=
  LinearEquiv.piCongrRight (fun _ => Representation.SL2FourNatural.action a)

noncomputable def adjustedCoordinates
    {D : Setup G} {g : G} (d : Hypothesis D g) [
      ((AlternatingFive.S₂ D g).subgroupOf (D.S g)).Normal] {s : ℕ}
    (c : NaturalLayer D g F4 s d.L_le_I) (a : SL(2, F4)) :
    UpperQuotient D g ≃* Multiplicative (Fin s → Fin 2 → F4) :=
  c.coordinates.trans (AddEquiv.toMultiplicative (adjustedAddEquiv a).toAddEquiv)

theorem adjustedCoordinates_equivariant
    {D : Setup G} {g : G} (d : Hypothesis D g) (hgen : D.I g = D.L)
    [((AlternatingFive.S₂ D g).subgroupOf (D.S g)).Normal]
    {s : ℕ} (c : NaturalLayer D g F4 s d.L_le_I)
    (a : SL(2, F4)) (k : D.L₁) (x : Section (second d) (core d)) :
    (adjustedCoordinates d c a
      (upperSectionEquiv d hgen c (sectionAction (second d) (core d) k x))).toAdd =
      fun j => ((c.model.trans (MulAut.conj a))
        (starProjection D (inclusion (residual_le_L D) k))).val *ᵥ
        (adjustedCoordinates d c a (upperSectionEquiv d hgen c x)).toAdd j := by
  let i : D.star D.L := starProjection D (inclusion (residual_le_L D) k)
  let ρ : Representation (ZMod 2) (D.star D.L) (Fin 2 → F4) :=
    Representation.SL2FourNatural.PointCommutator.representation.comp c.model.toMonoidHom
  have he (z : D.star D.L) (v : Fin 2 → F4) :
      (LinearEquiv.refl (ZMod 2) (Fin 2 → F4)) (ρ z v) =
      Representation.SL2FourNatural.PointCommutator.representation (c.model z)
          ((LinearEquiv.refl (ZMod 2) (Fin 2 → F4)) v) := by rfl
  have hi := Representation.innerIntertwiner_equivariant ρ
      Representation.SL2FourNatural.PointCommutator.representation c.model.toMonoidHom
      (LinearEquiv.refl (ZMod 2) (Fin 2 → F4)) he a i
  have hu := upperCoordinates_equivariant d hgen c k x
  apply funext
  intro j
  change (Representation.SL2FourNatural.action a)
      ((upperCoordinates d hgen c
        (sectionAction (second d) (core d) k x)).toAdd j) = _
  rw [hu]
  simp
  change (Representation.SL2FourNatural.action a)
      ((c.model i).val *ᵥ (upperCoordinates d hgen c x).toAdd j) =
    ((c.model.trans (MulAut.conj a)) i).val *ᵥ
      (Representation.SL2FourNatural.action a
        ((upperCoordinates d hgen c x).toAdd j))
  have hj := hi ((upperCoordinates d hgen c x).toAdd j)
  exact hj

theorem exists_aligned_natural_coordinates
    {D : Setup G} {g : G} (d : Hypothesis D g) (hgen : D.I g = D.L)
    [((AlternatingFive.S₂ D g).subgroupOf (D.S g)).Normal]
    {s : ℕ} (c : NaturalLayer D g F4 s d.L_le_I) :
    ∃ a : SL(2, F4),
      ((D.star D.U).subgroupOf (D.star D.L)).map
          (c.model.trans (MulAut.conj a)).toMonoidHom =
        Matrix.SpecialLinearGroup.upperUnipotent F4 ∧
      ((D.star D.L₁).subgroupOf (D.star D.L)).map
          (c.model.trans (MulAut.conj a)).toMonoidHom =
        Matrix.SpecialLinearGroup.rankOneBorel F4 ∧
      ∀ (k : D.L₁) (x : Section (second d) (core d)),
        (adjustedCoordinates d c a
          (upperSectionEquiv d hgen c
            (sectionAction (second d) (core d) k x))).toAdd =
          fun j => ((c.model.trans (MulAut.conj a))
            (starProjection D (inclusion (residual_le_L D) k))).val *ᵥ
            (adjustedCoordinates d c a
              (upperSectionEquiv d hgen c x)).toAdd j := by
  obtain ⟨a, hu, hL⟩ := exists_natural_alignment_conjugator d c
  refine ⟨a, hu, hL, ?_⟩
  intro k x
  exact adjustedCoordinates_equivariant d hgen c a k x


end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.NaturalParabolic
