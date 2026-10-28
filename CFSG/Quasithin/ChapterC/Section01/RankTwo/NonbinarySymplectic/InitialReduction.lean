module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.CharacteristicReduction
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Intrinsic initial reductions for nonbinary symplectic MS-pairs

The input retains the literal product, relative component, odd-index radical,
and actual two-core quotient. The component is the two-residual, hence normal.
Simplicity of the specified nonbinary symplectic group and MS3 identify the
centralizer of the original omega-center orbit with the ambient two-core.
This supplies a faithful FF action and positive even critical geometry without
assuming a natural module, a field of order four, or a commutator-core bound.

These are initial reductions, not the whole-core classification of C.1.32.
Source: Aschbacher--Smith C.1.31--32, printed pp.135--136; Meierfrankenfeld--
Stellmacher (1993), the opening of Section 3 and the reduction in Section 7.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit

variable {H F : Type*} [Group H] [Field F]

/-- The literal nonbinary symplectic specialization of C.1.31. None of the
module or whole-core conclusions of C.1.32 is included. -/
structure Input (K R : Subgroup H) (n : ℕ) (F : Type*) [Field F] where
  nonbinary : 1 < n
  field_card : Nat.card F = 2 ^ n
  sqtk : IsSQTK KnownSimple.IsKnownSimple H
  fitting : generalizedFitting H = pCore 2 H
  component : K.IsCComponent
  product : ∀ h : H, ∃ k ∈ K, ∃ r ∈ R, k * r = h
  radical : MSOddIndexRadical R
  characteristic : MSCharacteristicCondition R
  quotientEquiv : (K ⧸ pCore 2 K) ≃* Matrix.symplecticGroup (Fin 2) F

variable [Finite H] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)

include h

omit [Finite H] [Finite F] in
/-- The supplied marking identifies the center of the literal core quotient. -/
theorem Input.quotient_center : center (K ⧸ pCore 2 K) = ⊥ := by
  apply bot_unique
  intro x hx
  have hz := (centerCongr h.quotientEquiv ⟨x,hx⟩).property
  have he : h.quotientEquiv x = 1 :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot.le hz
  exact h.quotientEquiv.map_eq_one_iff.mp he

omit [Finite H] [Finite F] in
/-- The source's O₂,Z(K) is exactly O₂(K), with no odd central covering kernel. -/
theorem Input.centralPreimage_eq : centralPreimage (pCore 2 K) = pCore 2 K := by
  change (center (K ⧸ pCore 2 K)).comap (QuotientGroup.mk' _) = _
  rw [h.quotient_center]
  exact QuotientGroup.ker_mk' _

omit [Finite H] in
/-- The nonbinary assumption suffices for simplicity of the actual quotient. -/
theorem Input.quotient_simple : IsSimpleGroup (K ⧸ pCore 2 K) := by
  have hlarge : 3 < Nat.card F := by
    rw [h.field_card]
    exact lt_of_lt_of_le (by decide : 3 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Matrix.symplecticGroup (Fin 2) F) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  exact h.quotientEquiv.isSimpleGroup

omit [Finite F] [CharP F 2] in
/-- The product with the two-group radical identifies the original component. -/
theorem Input.residual_eq : pResidual 2 H = K :=
  component_eq_residual K R h.component h.radical.isPGroup h.product

omit [Finite F] [CharP F 2] in
/-- Normality is derived inside the input group, not imposed in a larger group. -/
theorem Input.component_normal : K.Normal := by
  rw [← h.residual_eq]
  infer_instance

omit [Finite F] [CharP F 2] in
/-- Characteristic two gives the required self-centralizing two-core. -/
theorem Input.core_selfCentralizing : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  simpa only [h.fitting] using (centralizer_generalizedFitting_le H)

omit [Finite F] [CharP F 2] in
/-- The radical cannot be trivial in a group with the specified component. -/
theorem Input.radical_ne_bot : R ≠ ⊥ := by
  intro hr
  have hq : pCore 2 H = ⊥ := le_bot_iff.mp (hr ▸ h.radical.twoCore_le)
  have ht : (⊤ : Subgroup H) ≤ ⊥ := by
    intro x _
    have hx : x ∈ centralizer (pCore 2 H : Set H) := by
      rw [hq]
      intro y hy
      have hy' : y = 1 := hy
      simp only [hy', one_mul, mul_one]
    exact hq ▸ h.core_selfCentralizing hx
  exact h.component.ne_bot (le_bot_iff.mp (le_top.trans ht))

/-- MS3 supplies faithfulness on the original omega-center orbit. -/
theorem Input.omegaOrbit_centralizer :
    centralizer (omegaOrbit R : Set H) = pCore 2 H := by
  let := h.component_normal
  let := h.quotient_simple
  exact MSCentralOrbit.omegaOrbit_centralizer K R h.radical.isPGroup h.radical_ne_bot
    h.radical.twoCore_le h.core_selfCentralizing h.product h.characteristic

/-- The full central omega layer has the same exact kernel. -/
theorem Input.centralOmega_centralizer :
    centralizer (omegaCenterIn (pCore 2 H) : Set H) = pCore 2 H :=
  MSCentralOrbit.centralOmega_centralizer R h.radical.twoCore_le
    h.core_selfCentralizing h.omegaOrbit_centralizer

/-- The FF action is the actual conjugation action of H/O₂(H) on Ω₁(Z(O₂(H))). -/
theorem Input.centralOmega_isFFModule :
    Representation.BinaryOffender.IsFFModule
      (Representation.NormalElementaryQuotient.representation
        (omegaCenterIn (pCore 2 H)) (QuotientGroup.mk' (pCore 2 H))
        (QuotientGroup.mk'_surjective _)
        ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) := by
  exact MSCentralOrbit.centralOmega_isFFModule R h.characteristic h.radical.isPGroup
    h.radical_ne_bot h.radical.twoCore_le h.core_selfCentralizing
    h.omegaOrbit_centralizer (QuotientGroup.mk' (pCore 2 H))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

/-- Every quotient-component premise is obtained on the literal quotient image. -/
theorem Input.component_image_structure :
    let B := K.map (QuotientGroup.mk' (pCore 2 H))
    K.Normal ∧ B.Normal ∧ IsSimpleGroup B ∧ IsQuasisimple B ∧
      centralizer (B : Set (H ⧸ pCore 2 H)) = ⊥ := by
  let := h.quotient_simple
  exact MSCentralOrbit.component_image_structure K R h.component
    h.radical.isPGroup h.product

/-- The genuine holomorph geometry has positive even critical distance. -/
theorem Input.positive_even_geometry :
    ∃ g : BinaryMS.MS93.Geometry R, 0 < g.b R ∧ Even (g.b R) :=
  exists_positive_even_geometry R h.radical.isPGroup h.radical_ne_bot
    h.characteristic h.radical.twoCore_le h.core_selfCentralizing h.omegaOrbit_centralizer

omit [Finite F] [CharP F 2] in
/-- Characteristic replacement preserves the embedded intrinsic commutator core.
No odd-index-radical assertion is made about the replacement. -/
theorem Input.characteristic_reduction :
    ∃ d : BinaryMS.MS93.CharacteristicReduction K R,
      d.overgroup.Normal ∧ MSCharacteristicCondition d.radical ∧
      pCore 2 d.overgroup ≤ d.radical ∧
      (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆).map d.overgroup.subtype =
        (blockU K).map K.subtype :=
  BinaryMS.MS93.component_characteristic_reduction K R h.component
    h.radical.isPGroup h.product h.radical.twoCore_le h.characteristic

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
