module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.SL3

/-!
# The SL₃ seed image in the literal central core section

The original seed inclusion V→O₂(L₁) followed by the original central
quotient has kernel exactly V₁. Natural coordinates therefore give its
image order q², and the map intertwines the original L₁ conjugation action.
In the exceptional GO case this image has order sixteen. The final consumer
uses this proved first-layer order to reduce the section-order premise to
the index of this specific image.

The second-layer index, central-commutator bound and fixed-free-five action
remain with qt-d-1222-natural-point-fixed-summand, as do the Sp₄ action,
TI centralizer control and final assembly. The enclosing source assembly
owner is qt-d-1222-natural-normalizer-source.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004, 11.1.5,
printed p.766, the two natural chief factors in the SL₃(4) branch.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Representation.BinaryOffender Representation.GoldschmidtONan
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.SL3
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m))

/-- Inclusion of the actual seed in the intrinsic point residual's core. -/
def seedCoreMap : V →* pCore 2 (f.Li 0) where
  toFun v := ⟨⟨v, (seed_le_first_core D S m f).trans (pCoreIn_le 2 _) v.property⟩, by
    obtain ⟨a,ha,he⟩ := seed_le_first_core D S m f v.property
    have he' : a = ⟨v, (seed_le_first_core D S m f).trans (pCoreIn_le 2 _) v.property⟩ := by
      apply Subtype.ext
      exact he
    exact he' ▸ ha⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Subtype.ext; rfl

/-- The seed maps into the literal central core section through the original inclusion. -/
def seedSectionMap : V →* CoreCentralSection (f.Li 0) :=
  (QuotientGroup.mk' ((center (f.Li 0)).subgroupOf (pCore 2 (f.Li 0)))).comp
    (seedCoreMap D S m f)

/-- Its kernel is exactly the caller's first line, not a substituted model line. -/
theorem seedSectionMap_ker :
    (seedSectionMap D S m f).ker = (f.Vi 0).subgroupOf V := by
  ext v
  change seedCoreMap D S m f v ∈
    (QuotientGroup.mk' ((center (f.Li 0)).subgroupOf (pCore 2 (f.Li 0)))).ker ↔
      (v : G) ∈ f.Vi 0
  rw [QuotientGroup.ker_mk', ←seed_fixed_first D S m f]
  constructor
  · intro hv
    refine ⟨v.property,?_⟩
    intro a ha
    exact congrArg Subtype.val ((mem_center_iff.mp hv) ⟨a,ha⟩)
  · intro hv
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    exact hv.2 a a.property

/-- The image of the original seed has the field-plane order q². -/
theorem seedSectionMap_range_card :
    Nat.card (seedSectionMap D S m f).range = (2 ^ S.field.degree) ^ 2 := by
  have hV : Nat.card V = (2 ^ S.field.degree) ^ 3 := by
    rw [Nat.card_congr (LocalGeometry.SL3.naturalEquiv D S m).toEquiv]
    change Nat.card (Fin 3 → S.field.Carrier) = _
    rw [Module.natCard_eq_pow_finrank (K := S.field.Carrier),
      Module.finrank_fin_fun,S.field.card_eq]
  have hline : Nat.card (f.Vi 0) = 2 ^ S.field.degree := by
    let U : Submodule S.field.Carrier (Fin 3 → S.field.Carrier) := f.space 0
    have hc := Nat.card_congr (LocalGeometry.SL3.subspaceEquiv D S m U).toEquiv
    change Nat.card (f.Vi 0) = Nat.card U at hc
    rw [hc,Module.natCard_eq_pow_finrank (K := S.field.Carrier)]
    rw [show Module.finrank S.field.Carrier U = 1 from f.dimension 0]
    change Nat.card S.field.Carrier ^ 1 = _
    rw [pow_one, S.field.card_eq]
  have hk : Nat.card (seedSectionMap D S m f).ker = 2 ^ S.field.degree := by
    rw [seedSectionMap_ker]
    exact (Nat.card_congr (subgroupOfEquivOfLe (D.centralQuotientPreimage_le _)).toEquiv).trans hline
  have h := (seedSectionMap D S m f).ker.card_mul_index
  rw [index_ker,hk,hV] at h
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ S.field.degree from pow_pos (by decide) _)
  exact h.trans (by ring)

/-- Conjugation on the first layer is the restriction of the literal inner action. -/
theorem seedSectionMap_conjugation (a : f.Li 0) (v : V) :
    ChiefSection.innerAction (f.Li 0) a (seedSectionMap D S m f v) =
      seedSectionMap D S m f (V.normalizerMonoidHom
        (inclusion (((localResidual_le _).trans inf_le_left).trans D.normalizes) a) v) := by
  rfl

/-- The exceptional GO parameters make this particular seed image have order sixteen. -/
theorem exceptional_seedSection_card (X : Subgroup G)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)) :
    Nat.card (seedSectionMap D S m f).range = 16 := by
  rw [seedSectionMap_range_card, (chosen_exceptional_parameters D S f X hcenter hfixed he).1]
  norm_num

/-- The remaining second chief factor supplies the total section order; the
first factor's order is discharged on its literal image here. -/
theorem exceptional_escape_of_short_section_index (hb : ChapterC.IsShort L)
    (X : Subgroup G)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (h : Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hc : ⁅pCore 2 (f.Li 0), pCore 2 (f.Li 0)⁆ ≤ center (f.Li 0))
    (hindex : (seedSectionMap D S m f).range.index = 16)
    (B : Subgroup (MulAut (CoreCentralSection (f.Li 0))))
    (hB : B ≤ (ChiefSection.innerAction (f.Li 0)).range)
    (hBcard : Nat.card B = 5)
    (hBfixed : FixedPoints.subgroup B (CoreCentralSection (f.Li 0)) = ⊥) : False := by
  have hcard : Nat.card (CoreCentralSection (f.Li 0)) = 256 := by
    rw [←(seedSectionMap D S m f).range.card_mul_index,
      exceptional_seedSection_card D S m f X hcenter hfixed he,hindex]
  exact exceptional_escape_of_short_sections D S m f hb X hescape hcenter h hfixed he
    hc hcard B hB hBcard hBfixed

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.SL3
