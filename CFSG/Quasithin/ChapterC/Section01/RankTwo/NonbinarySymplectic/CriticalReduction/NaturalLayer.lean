module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NaturalRecognition

/-!
# The natural cover on the characteristic replacement

Natural recognition on the replacement gives its original field degree.
The canonical moved/fixed projection is a cover for the literal derived
symplectic actor, retaining the entire fixed central kernel.
Source: MS93 (3.2)(vi), pp.863--866, applied after Section 7, pp.932--933.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
private theorem initialCover_of_moved_natural
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) J V) (C : Subgroup J) [C.Normal]
    {n : ℕ} (hn : 1 < n)
    (hnat : IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) ∧
      ∃ E : BinaryField, E.degree = n ∧
        Nonempty (ActionEquiv ((MovedSection.ofNormal ρ C).action.comp C.subtype)
          (binarySymplectic E))) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ e : ActionEquiv ((MovedSection.ofNormal ρ C).action.comp C.subtype)
          (binaryNatural (K := E.Carrier)),
        IsCover (MovedSection.coverProjection (MovedSection.ofNormal ρ C) e) := by
  obtain ⟨hi,E,hE,⟨e⟩⟩ := hnat
  have hlarge : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide) hn)
  let s := MovedSection.ofNormal ρ C
  let e' : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)) :=
    Sp4Four.derivedNaturalActionEquiv hlarge (s.action.comp C.subtype) e
  exact ⟨E,hE,e',MovedSection.coverProjection_isCover s hi e'⟩

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

/-- The original moved/fixed projection is a cover for the actual natural
symplectic derived action, retaining the field degree of the input marking. -/
theorem Input.replacement_centralOmega_initial_cover :
    let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
    let : C.Normal := (h.replacement_component_image_structure d).2.1
    let ρ := NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 d.overgroup)) (QuotientGroup.mk' (pCore 2 d.overgroup))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)
    let s := MovedSection.ofNormal ρ C
    ∃ E : BinaryField, E.degree = n ∧
      ∃ e : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)),
        IsCover (MovedSection.coverProjection s e) := by
  dsimp only
  let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  exact initialCover_of_moved_natural _ C h.nonbinary
    (h.replacement_centralOmega_moved_natural d)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
