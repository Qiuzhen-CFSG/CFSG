module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.ThompsonImage.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.MaximalImages
public import Theory.Representation.HexacodeAction.ThompsonOffenders
public import Theory.Representation.BinaryOffender.FixedCodimTransport

/-!
# The full hexacode action on an original elementary subgroup

The literal plus quotient acts on an ambient elementary subgroup U. Faithful
hexacode coordinates identify its kernel with the exact centralizer of U.
Maximum elementary subgroups of the source Sylow subgroup consequently have
best-offender images. No exceptional-block predicate or core reconstruction is
used here.

Source: Aschbacher–Smith, 13.6.22, printed p.932, using B.2.5–7 and B.4.2(8).
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixNormalizer
open ComponentSelection
variable {G : Type*} [Group G]
variable (K L T U : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 U]

/-- Faithful coordinates for the full literal plus action on U. -/
structure Model where
  embedding : Gplus K L T z v hL hz →* Atlas.Codes.HexAutomorphisms
  injective : Function.Injective embedding
  coordinates : Additive U ≃ₗ[ZMod 2] Atlas.Codes.hexacode
  conjugation : ∀ (g : plusActor K L T v) (u : Additive U),
    ((coordinates.symm
      (Hexacode.action (embedding (plusMk K L T z v hL hz g)) (coordinates u))).toMul : G) =
        (g : G) * (u.toMul : G) * (g : G)⁻¹

variable {K L T U z v hL hz}
variable (d : Model K L T U z v hL hz)

/-- Transport of the full model action to the original U. -/
noncomputable def Model.action :
    Representation (ZMod 2) (Gplus K L T z v hL hz) (Additive U) where
  toFun g := d.coordinates.symm.toLinearMap.comp
    ((Hexacode.action (d.embedding g)).comp d.coordinates.toLinearMap)
  map_one' := by apply LinearMap.ext; intro u; simp
  map_mul' a b := by apply LinearMap.ext; intro u; simp

/-- Both actions use the same vector coordinates. -/
theorem Model.intertwining (g : Gplus K L T z v hL hz) (u : Additive U) :
    d.coordinates (d.action g u) = Hexacode.action (d.embedding g) (d.coordinates u) :=
  d.coordinates.apply_symm_apply _

/-- The transported action is literal ambient conjugation. -/
theorem Model.action_conjugation (g : plusActor K L T v) (u : Additive U) :
    ((d.action (plusMk K L T z v hL hz g) u).toMul : G) =
      (g : G) * (u.toMul : G) * (g : G)⁻¹ := d.conjugation g u

/-- The original U-action remains faithful. -/
theorem Model.action_injective : Function.Injective d.action := by
  intro a b he
  apply d.injective
  apply Hexacode.action_injective
  apply LinearMap.ext
  intro w
  have hc := congrArg d.coordinates (LinearMap.congr_fun he (d.coordinates.symm w))
  simpa only [d.intertwining, d.coordinates.apply_symm_apply] using hc

/-- Fixed vectors of an actual plus image are actual centralizing elements. -/
theorem Model.mem_fixedSpace_image (D : Subgroup G)
    (hD : D ≤ plusActor K L T v) (u : Additive U) :
    u ∈ fixedSpace d.action (plusImage K L T z v hL hz D) ↔
      (u.toMul : G) ∈ centralizer (D : Set G) := by
  constructor
  · intro hu g hg
    have he := congrArg (fun w : Additive U => (w.toMul : G))
      (hu ⟨plusMk K L T z v hL hz ⟨g, hD hg⟩,
        mem_map.mpr ⟨⟨g, hD hg⟩, hg, rfl⟩⟩)
    change ((d.action (plusMk K L T z v hL hz ⟨g, hD hg⟩) u).toMul : G) = _ at he
    rw [d.action_conjugation] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hu a
    obtain ⟨g, hg, he⟩ := a.property
    change d.action a.val u = u
    rw [← he]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [d.action_conjugation, hu g hg, mul_inv_cancel_right]

/-- Nontrivial images of the original maximum elementary subgroups are best offenders. -/
theorem Model.maxElementary_isBestOffender [Finite G]
    (hUT : U ≤ Tv T v) (hUN : plusActor K L T v ≤ normalizer (U : Set G))
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (Tv T v))
    (hne : plusImage K L T z v hL hz A ≠ ⊥) :
    IsBestOffender d.action (plusImage K L T z v hL hz A) := by
  let H := plusActor K L T v
  have hUH : U ≤ H := hUT.trans le_sup_right
  let U0 := U.subgroupOf H
  have : U0.Normal := normal_subgroupOf_of_le_normalizer hUN
  have : IsElementaryAbelian 2 U0 := IsElementaryAbelian.subgroupOf hUH
  let e : U ≃* U0 := (subgroupOfEquivOfLe hUH).symm
  let E : Additive U0 ≃ₗ[ZMod 2] Additive U :=
    LinearEquiv.ofBijective (e.symm.toMonoidHom.toAdditive.toZModLinearMap 2) e.symm.bijective
  have he (u : Additive U0) : ((E u).toMul : G) = ((u.toMul : H) : G) := rfl
  let q := plusMk K L T z v hL hz
  have hq := plusMk_surjective K L T z v hL hz
  have hker : q.ker = centralizer (U0 : Set H) := by
    ext g
    change q g = 1 ↔ g ∈ centralizer (U0 : Set H)
    constructor
    · intro hg u hu
      apply Subtype.ext
      have hfix : d.action (q g) (E (Additive.ofMul ⟨u, hu⟩)) =
          E (Additive.ofMul ⟨u, hu⟩) := by rw [hg, map_one]; rfl
      have heq := congrArg (fun w : Additive U => (w.toMul : G)) hfix
      rw [d.action_conjugation, he] at heq
      exact (mul_inv_eq_iff_eq_mul.mp heq).symm
    · intro hg
      apply d.action_injective
      rw [map_one]
      apply LinearMap.ext
      intro u
      have hc : (u.toMul : G) * (g : G) = (g : G) * (u.toMul : G) :=
        congrArg H.subtype (hg (e u.toMul) (e u.toMul).property)
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [d.action_conjugation, ← hc, mul_inv_cancel_right]
      rfl
  let ρ := NormalElementaryQuotient.representation U0 q hq hker
  have hE (a : Gplus K L T z v hL hz) (u : Additive U0) :
      E (ρ a u) = d.action a (E u) := by
    obtain ⟨g, rfl⟩ := hq a
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [he, d.action_conjugation, he]
    exact congrArg H.subtype (NormalElementaryQuotient.representation_apply U0 q hq hker g u)
  have hAH : A ≤ H := hA.1.trans le_sup_right
  have hAm : A.subgroupOf H ∈ elementaryAbelianMaxSubgroups ((Tv T v).subgroupOf H) := by
    have : IsElementaryAbelian 2 A := hA.2.1
    refine ⟨comap_mono hA.1, IsElementaryAbelian.subgroupOf hAH, ?_⟩
    intro B hBS hB
    have : IsElementaryAbelian 2 B := hB
    calc
      Nat.card B = Nat.card (B.map H.subtype) := (card_map_of_injective H.subtype_injective).symm
      _ ≤ Nat.card A := hA.2.2 _
        ((map_mono hBS).trans_eq (map_subgroupOf_eq_of_le le_sup_right))
        (IsElementaryAbelian.map H.subtype)
      _ = Nat.card (A.subgroupOf H) := (Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).symm
  have hbest := CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
    U0 q hq hker ((Tv T v).subgroupOf H) (A.subgroupOf H) (comap_mono hUT) hAm hne
  have hdim (B : Subgroup (Gplus K L T z v hL hz)) :
      Module.finrank (ZMod 2) (fixedSpace ρ B) = Module.finrank (ZMod 2) (fixedSpace d.action B) := by
    have hh := fixedSpace_map_equivariant ρ d.action (MonoidHom.id _) E hE B
    rw [Subgroup.map_id] at hh
    rw [← hh]
    exact (Submodule.equivMapOfInjective E.toLinearMap E.injective _).finrank_eq
  refine ⟨hbest.1, ?_⟩
  intro B hBA
  have hb : weight ρ B ≤ weight ρ (plusImage K L T z v hL hz A) := hbest.2 B hBA
  simpa only [weight, hdim] using hb

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixNormalizer
