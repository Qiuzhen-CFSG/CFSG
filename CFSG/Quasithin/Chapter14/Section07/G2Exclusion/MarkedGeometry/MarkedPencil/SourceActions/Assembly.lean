module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.ResidualAction

/-!+# Local marking and residual action in the source quotient

The actual Sylow subgroup T meets the preimage of G₂(2)′ in a Sylow subgroup.
Its image supplies the derived Sylow needed by the line calculation. Thus the
earlier orders and local actions construct both the doubly singular line V/V₁
and its point V₂/V₁. Their markings then discharge the pencil and residual
theorems, on the same literal quotient U/(V₁.subgroupOf U).

The two final applications establish 14.7.55(1),(2),(3),(6) conditional only on
the earlier source identities and the actual module identification. The Weyl
case uses [V,L₁]V₁ = V. The natural case needs only T-invariance. Both retain
Y = O²(C_H(V₂)), its normal product with T and its actual quotient action.
Here H is the source local group, so normality of U is relative to H.

The 14.7.54 identification and earlier local identities are supplied by
qt-14-07-g2-exclusion; qt-14-07-g2-marked-pencil retains their final discharge.
The separate offender deduction retains its explicit B.4.6 and clause-(4)
inputs, as described in Offenders.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed p.1066,
PDF p.1083, 14.7.55. The model imports use the attributed ATLAS port
(LICENSES/ATLAS.txt); no additional ATLAS source is copied.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions
open Atlas.G2 Atlas.G2.Natural Atlas.SplitOctonion Atlas.G2.BinaryParabolicPair
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
open Subgroup LineMarking ResidualAction

variable {H : Type*} [Group H] [Finite H]

/-- The actual source Sylow image contains a Sylow of the actual derived model.
The witness is constructed by normal restriction and a surjective image. -/
theorem source_derived_sylow (π : H →* Model (ZMod 2))
    (hJ : commutator (Model (ZMod 2)) ≤ π.range) (T : Sylow 2 H) :
    ∃ S : Sylow 2 DerivedModel,
      (S : Subgroup DerivedModel).map DerivedModel.subtype ≤
        (π.comp (T : Subgroup H).subtype).range := by
  let D := DerivedModel.comap π
  let j : D →* DerivedModel := (π.comp D.subtype).codRestrict DerivedModel (fun d => d.property)
  have hj : Function.Surjective j := by
    intro d
    obtain ⟨h,hh⟩ := hJ d.property
    refine ⟨⟨h, ?_⟩, Subtype.ext hh⟩
    change π h ∈ DerivedModel
    rw [hh]
    exact d.property
  obtain ⟨R,hR⟩ := T.exists_sylow_map_eq_inf_of_normal D
  refine ⟨R.mapSurjective hj, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  have he : DerivedModel.subtype.comp j = π.comp D.subtype := rfl
  rw [he, ← Subgroup.map_map, hR, MonoidHom.range_comp, Subgroup.range_subtype]
  exact Subgroup.map_mono inf_le_left

/-- Clauses (1),(2),(3),(6) for the natural module, with the singular markings
constructed from the earlier local orders and the actual Sylow action. -/
theorem natural_source_actions
    (U V₁ V₂ V : Subgroup H) [U.Normal] [(V₁.subgroupOf U).Normal]
    [IsElementaryAbelian 2 V₁] (h12 : V₁ ≤ V₂) (h2V : V₂ ≤ V) (hVU : V ≤ U)
    (hcentral : (⊤ : Subgroup H) ≤ centralizer (V₁ : Set H))
    (π : H →* Model (ZMod 2)) (hJ : commutator (Model (ZMod 2)) ≤ π.range)
    (hk : IsPGroup 2 π.ker)
    (e : Multiplicative (Space (ZMod 2)) ≃* U ⧸ V₁.subgroupOf U)
    (hact : ∀ (h : H) (u : U), action (ZMod 2) (π h)
        (e.symm (QuotientGroup.mk' (V₁.subgroupOf U) u)).toAdd =
      (e.symm (QuotientGroup.mk' (V₁.subgroupOf U)
        ⟨h * (u : H) * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩)).toAdd)
    (hcardV : Nat.card ((V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 4)
    (hcardV₂ : Nat.card ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 2)
    (T : Sylow 2 H) (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hT₂ : (T : Subgroup H) ≤ normalizer (V₂ : Set H)) :
    let q := QuotientGroup.mk' (V₁.subgroupOf U)
    let geom := naturalQuotientGeometry (V₁.subgroupOf U) e
    let point := (V₂.subgroupOf U).map q
    let span := quotientPencilSpan geom point
    let preimage := (span.comap q).map U.subtype
    ∃ L : ZeroProductLine (ZMod 2), ∃ p : SingularPoints (ZMod 2),
      (V.subgroupOf U).map q = geom.line L ∧ geom.point p = point ∧ pointOnLine p L ∧
      Nat.card (quotientPencil geom point) = 3 ∧ Nat.card span = 8 ∧
      Nonempty ((sourceResidual V₂ ⊔ (T : Subgroup H) : Subgroup H) ⧸
        pCore 2 (sourceResidual V₂ ⊔ (T : Subgroup H) : Subgroup H) ≃* Equiv.Perm (Fin 3)) ∧
      (⁅preimage,sourceResidual V₂⁆.subgroupOf U).map q = span ∧
      ∀ B ∈ quotientPencil geom point, ∀ C ∈ quotientPencil geom point,
        ∃ y ∈ sourceResidual V₂, B.map (quotientActor (action (ZMod 2)) e (π y)) = C := by
  dsimp only
  have hn : (T : Subgroup H) ≤ normalizer (U : Set H) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨S,hS⟩ := source_derived_sylow π hJ T
  obtain ⟨L,hL⟩ := natural_source_line_of_local_actions U V₁ V T e hcardV
    (π.comp (T : Subgroup H).subtype) hn hTV (fun t u => hact t u) S hS
  have hle : (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) ≤
      (transportGeometry naturalMap.geometry e).line L := by
    change _ ≤ (naturalQuotientGeometry (V₁.subgroupOf U) e).line L
    rw [← hL]
    exact Subgroup.map_mono (Subgroup.comap_mono h2V)
  obtain ⟨p,hp,hpL⟩ := point_of_card_two_le_line naturalMap e _ hcardV₂ L hle
  obtain ⟨hc,hs⟩ := natural_source_pencil U V₁ V₂ e p hp.symm
  exact ⟨L,p,hL,hp,hpL,hc,hs,
    source_residual_action U V₁ V₂ h12 (h2V.trans hVU) hcentral
      naturalMap (action (ZMod 2)) naturalMap_equivariant π hJ e hact p hp.symm T hT₂ hk⟩

/-- Clauses (1),(2),(3),(6) for the Weyl module. The actual local L₁ commutator
identity removes the nonsingular invariant planes before marking the point. -/
theorem weyl_source_actions
    (U V₁ V₂ V L₁ : Subgroup H) [U.Normal] [(V₁.subgroupOf U).Normal]
    [IsElementaryAbelian 2 V₁] (h12 : V₁ ≤ V₂) (h2V : V₂ ≤ V) (hVU : V ≤ U)
    (hlocal : ⁅V,L₁⁆ ⊔ V₁ = V)
    (hcentral : (⊤ : Subgroup H) ≤ centralizer (V₁ : Set H))
    (π : H →* Model (ZMod 2)) (hJ : commutator (Model (ZMod 2)) ≤ π.range)
    (hk : IsPGroup 2 π.ker)
    (e : Multiplicative (TraceZero (ZMod 2)) ≃* U ⧸ V₁.subgroupOf U)
    (hact : ∀ (h : H) (u : U), traceZeroAction (ZMod 2) (π h)
        (e.symm (QuotientGroup.mk' (V₁.subgroupOf U) u)).toAdd =
      (e.symm (QuotientGroup.mk' (V₁.subgroupOf U)
        ⟨h * (u : H) * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩)).toAdd)
    (hcardV : Nat.card ((V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 4)
    (hcardV₂ : Nat.card ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) = 2)
    (T : Sylow 2 H) (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hT₂ : (T : Subgroup H) ≤ normalizer (V₂ : Set H)) :
    let q := QuotientGroup.mk' (V₁.subgroupOf U)
    let geom := weylQuotientGeometry (V₁.subgroupOf U) e
    let point := (V₂.subgroupOf U).map q
    let span := quotientPencilSpan geom point
    let preimage := (span.comap q).map U.subtype
    ∃ L : ZeroProductLine (ZMod 2), ∃ p : SingularPoints (ZMod 2),
      (V.subgroupOf U).map q = geom.line L ∧ geom.point p = point ∧ pointOnLine p L ∧
      Nat.card (quotientPencil geom point) = 3 ∧ Nat.card span = 8 ∧
      Nonempty ((sourceResidual V₂ ⊔ (T : Subgroup H) : Subgroup H) ⧸
        pCore 2 (sourceResidual V₂ ⊔ (T : Subgroup H) : Subgroup H) ≃* Equiv.Perm (Fin 3)) ∧
      (⁅preimage,sourceResidual V₂⁆.subgroupOf U).map q = span ∧
      ∀ B ∈ quotientPencil geom point, ∀ C ∈ quotientPencil geom point,
        ∃ y ∈ sourceResidual V₂, B.map (quotientActor (traceZeroAction (ZMod 2)) e (π y)) = C := by
  dsimp only
  have hn (B : Subgroup H) : B ≤ normalizer (U : Set H) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨S,hS⟩ := source_derived_sylow π hJ T
  obtain ⟨L,hL,⟨p,hp,hpL⟩,hc,hs⟩ := weyl_source_point_and_pencil_of_local_actions
    U V₁ V₂ V L₁ T e hcardV hcardV₂ h2V hVU hlocal
    (π.comp L₁.subtype) (π.comp (T : Subgroup H).subtype) (hn L₁) (hn T) hTV
    (fun l u => hact l u) (fun t u => hact t u) S hS
  exact ⟨L,p,hL,hp,hpL,hc,hs,
    source_residual_action U V₁ V₂ h12 (h2V.trans hVU) hcentral
      weylMap (traceZeroAction (ZMod 2)) weylMap_equivariant π hJ e hact p hp.symm T hT₂ hk⟩

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions
