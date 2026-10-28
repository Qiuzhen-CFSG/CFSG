module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.FrattiniBranch
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.NaturalRecognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.NaturalLayerCover
public import Theory.Representation.NormalElementaryQuotient.IrrPlusCommutator

/-!
# The intrinsic nonbinary MS initial layer

All hypotheses of FF natural recognition come from the actual MS-pair.
Faithfulness identifies the omega orbit commutator with the moved central
omega layer, and the canonical projection is a natural symplectic cover.
Source: MS93 (3.2)(vi), before the field restriction in (3.7).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)

include h

omit [Finite F] [CharP F 2] in
/-- The actual quotient-component image has the order of the supplied Sp₄ marking. -/
theorem Input.component_image_card_sp :
    Nat.card (K.map (QuotientGroup.mk' (pCore 2 H))) =
      Nat.card (Matrix.symplecticGroup (Fin 2) F) :=
  (Nat.card_congr (cComponentTwoCoreQuotientEquiv h.component).symm.toEquiv).trans
    (Nat.card_congr h.quotientEquiv.toEquiv)

/-- The literal omega-center action has natural moved quotient of degree n.
The source hypotheses supply faithfulness, SQTK and all FF premises. -/
theorem Input.centralOmega_moved_natural :
    let C := K.map (QuotientGroup.mk' (pCore 2 H))
    let : C.Normal := h.component_image_structure.2.1
    let ρ := NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 H)) (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)
    IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) ∧
      ∃ E : BinaryField, E.degree = n ∧
        Nonempty (ActionEquiv ((MovedSection.ofNormal ρ C).action.comp C.subtype)
          (binarySymplectic E)) := by
  obtain ⟨hK,hC,hs,hq,hcent⟩ := h.component_image_structure
  let := hK
  let := hC
  let := hs
  let := hq
  dsimp only
  apply ff_card_sp_moved_natural _ _ F h.field_card h.nonbinary
    h.component_image_card_sp hcent h.component_image_sqtk
  · exact NormalElementaryQuotient.representation_injective _ _ _ _
  · exact h.centralOmega_isFFModule

/-- The original omega orbit and full central omega layer have the same
literal commutator with K; no fully moved or field-four premise is needed. -/
theorem Input.initialCore_eq :
    ⁅omegaOrbit R,K⁆ = ⁅omegaCenterIn (pCore 2 H),K⁆ := by
  let C := K.map (QuotientGroup.mk' (pCore 2 H))
  obtain ⟨_,hC,hs,hq,_⟩ := h.component_image_structure
  let := hC
  let := hs
  let := hq
  let : IsElementaryAbelian 2 (omegaOrbit R) :=
    omegaOrbit_elementary R h.radical.twoCore_le h.core_selfCentralizing
  have hne : C ≠ ⊥ := by
    intro hz
    have hc := h.component_image_card_sp
    have hlo := card_symplectic_ge F h.field_card h.nonbinary
    change Nat.card C = _ at hc
    rw [hz,card_bot] at hc
    omega
  exact NormalElementaryQuotient.commutator_eq_of_irrPlus (omegaOrbit R)
    (omegaCenterIn (pCore 2 H))
    (omegaOrbit_le_centralOmega R h.radical.twoCore_le h.core_selfCentralizing)
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.omegaOrbit_centralizer.symm)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)
    K C rfl hne h.centralOmega_moved_natural.1

/-- The original moved/fixed projection is a cover for the actual natural
symplectic derived action, retaining the field degree of the input marking. -/
theorem Input.centralOmega_initial_cover :
    let C := K.map (QuotientGroup.mk' (pCore 2 H))
    let : C.Normal := h.component_image_structure.2.1
    let ρ := NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 H)) (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)
    let s := MovedSection.ofNormal ρ C
    ∃ E : BinaryField, E.degree = n ∧
      ∃ e : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)),
        IsCover (MovedSection.coverProjection s e) := by
  dsimp only
  obtain ⟨hi,E,hdegree,⟨e⟩⟩ := h.centralOmega_moved_natural
  let C := K.map (QuotientGroup.mk' (pCore 2 H))
  let : C.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal
    (NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 H)) (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C
  have hlarge : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hdegree]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let e' : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)) :=
    Sp4Four.derivedNaturalActionEquiv hlarge (s.action.comp C.subtype) e
  exact ⟨E,hdegree,e',MovedSection.coverProjection_isCover s hi e'⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
