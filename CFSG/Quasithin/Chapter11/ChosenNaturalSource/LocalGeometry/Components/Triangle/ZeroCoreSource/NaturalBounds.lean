module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.ReducedMarking

/-!
# Natural sections bound the original Sylow subgroup

The natural section divides the full two-core, and the original quotient
contributes its entire two-part to |L|. Thus the original Sylow intersection
has order at least 2¹², and at least 2¹⁶ for either nonlinear natural model.
Its literal inclusion in S₀X excludes the linear and symplectic DGS rows,
and excludes both nonlinear original models from the remaining G₂ row.
No complement to a core or to the natural section is used.

Source: Aschbacher--Smith 11.1.2, printed p.762, applied to the original
natural section from 11.0.2; concrete full-Borel orders from DGS (15.2).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
open ChapterF.Source ChapterF.Source.SuzukiContainment
open ChapterF.Source.DGS85.OriginalExtension
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {L V : Subgroup G} (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

omit [Finite G] in
/-- The natural section and the full original quotient both contribute to |L|.
The quotient kernel is retained, and no complement is used. -/
theorem natural_product_dvd_component :
    Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) ∣ Nat.card L := by
  have hc : Nat.card D.chosenCentralQuotient ∣ Nat.card (pCore 2 L) := by
    have hv := Subgroup.card_dvd_of_surjective D.toCentralQuotient D.toCentralQuotient_surjective
    have hh := hv.trans (card_dvd_of_le D.le_componentCore)
    rwa [pCoreIn,card_map_of_injective L.subtype_injective] at hh
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 L),mul_comm]
  exact Nat.mul_dvd_mul (dvd_refl _) hc

private theorem large_innerSylow
    (c : Coordinates D S.field)
    (hv : 256 ∣ Nat.card D.chosenCentralQuotient)
    (hq : 256 ∣ Nat.card (L ⧸ pCore 2 L)) :
    65536 ≤ Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) := by
  have hd : 2^16 ∣ Nat.card L := by
    apply dvd_trans ?_ (natural_product_dvd_component D)
    exact (show 2^16 = (256:ℕ)*256 by decide) ▸ Nat.mul_dvd_mul hv hq
  have hdP := c.innerSylow.pow_dvd_card_of_pow_dvd_card hd
  have hh := Nat.le_of_dvd (Nat.card_pos (α := c.innerSylow)) hdP
  have he : Nat.card c.innerSylow = Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) := by
    rw [c.innerSylow_coe, ← inf_subgroupOf_right (T : Subgroup G) L]
    exact (Nat.card_congr (subgroupOfEquivOfLe (show (T : Subgroup G) ⊓ L ≤ L from inf_le_right)).toEquiv)
  rwa [he] at hh

/-- The original Sp₄ natural core and quotient force an inner Sylow of order ≥2¹⁶. -/
theorem sp4_innerSylow_large
    (m : CFSG.Quasithin.ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := S.field.Carrier) 2)))
    (hfour : S.field.degree = 2) :
    65536 ≤ Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) := by
  apply large_innerSylow D S (.sp4 m)
  · rw [Nat.card_congr m.linearEquiv.toEquiv,Nat.card_fun,Nat.card_sum,Nat.card_fin,
      S.field.card_eq,hfour]
    decide
  · rw [Nat.card_congr m.groupEquiv.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,
      S.field.card_eq,hfour]
    decide

/-- The original G₂ natural core and quotient give the same sufficient lower bound. -/
theorem g2_innerSylow_large
    (m : CFSG.Quasithin.ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
      (Representation.restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (hfour : S.field.degree = 2) :
    65536 ≤ Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) := by
  apply large_innerSylow D S (.g2 m)
  · rw [Nat.card_congr m.linearEquiv.toEquiv,
      Module.natCard_eq_pow_finrank (K := S.field.Carrier),Atlas.G2.Natural.finrank_space,
      S.field.card_eq,hfour]
    decide
  · rw [Nat.card_congr m.groupEquiv.toEquiv,Atlas.G2.card_Model,S.field.card_eq,hfour]
    decide

/-- Every original natural model already has an inner Sylow of order at least 2¹². -/
theorem natural_innerSylow_large (c : Coordinates D S.field) (hfour : S.field.degree = 2) :
    4096 ≤ Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) := by
  cases c with
  | sl3 m =>
    have hv : 64 ∣ Nat.card D.chosenCentralQuotient := by
      rw [Nat.card_congr m.linearEquiv.toEquiv,Nat.card_fun,Nat.card_fin,S.field.card_eq,hfour]
      decide
    have hq : 64 ∣ Nat.card (L ⧸ pCore 2 L) := by
      rw [Nat.card_congr m.groupEquiv.toEquiv]
      have hu := (Matrix.PSL3.LinearThree.unipotentSL S.field.Carrier).card_subgroup_dvd_card
      rwa [Matrix.PSL3.LinearThree.card_unipotentSL,S.field.card_eq,hfour] at hu
    have hd : 2^12 ∣ Nat.card L :=
      (show 2^12 ∣ Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) from
        by simpa only [show (64 * 64 : ℕ) = 2^12 by decide] using Nat.mul_dvd_mul hv hq).trans (natural_product_dvd_component D)
    let c : Coordinates D S.field := .sl3 m
    have hh := Nat.le_of_dvd (Nat.card_pos (α := c.innerSylow))
      (c.innerSylow.pow_dvd_card_of_pow_dvd_card hd)
    have he : Nat.card c.innerSylow = Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) := by
      rw [c.innerSylow_coe, ← inf_subgroupOf_right (T : Subgroup G) L]
      exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
    rwa [he] at hh
  | sp4 m => exact (by decide : 4096 ≤ 65536).trans (sp4_innerSylow_large D S m hfour)
  | g2 m => exact (by decide : 4096 ≤ 65536).trans (g2_innerSylow_large D S m hfour)

/-- On the original subgroup inclusions, the linear and symplectic Borels
are too small. The surviving comparison keeps the whole G₂(4) diagram. -/
theorem g2_of_fieldFour_comparison (c : Coordinates D S.field)
    {K₀ L₂ X : Subgroup G} (hX : IsCartan T L X) (hfour : S.field.degree = 2)
    (hc : FieldFourComparison T X K₀ L₂) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
      ∃ b : Bool, Nonempty (Iso (originalTriangle T X K₀ L₂) (G2Native.amalgam F b)) := by
  have hle : Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) ≤ Nat.card (overlap T X) :=
    Nat.le_of_dvd (Nat.card_pos (α := overlap T X))
      (card_dvd_of_le ((innerSylow_le_commonTwo c hX).trans le_sup_left))
  have hl := (natural_innerSylow_large D S c hfour).trans hle
  cases hc with
  | linear F hF b e =>
    have hp : Nat.card (overlap T X) ≤ 2880 := by
      rw [Nat.card_congr e.some.middle.toEquiv]
      have hm : Nat.card (Matrix.PSL3.LinearThree.borel F) ≤
          Nat.card (Matrix.PSL3.LinearThree.borelSL F) :=
        Nat.le_of_dvd (Nat.card_pos (α := Matrix.PSL3.LinearThree.borelSL F))
          ((Matrix.PSL3.LinearThree.borelSL F).card_map_dvd (Matrix.PSL3.projection F))
      apply hm.trans
      have hn : Nat.card (Matrix.PSL3.LinearThree.borelSL F) ≤
          Nat.card (Matrix.PSL3.SmallCompletion.parabolicSL F false) :=
        Nat.le_of_dvd (Nat.card_pos (α := Matrix.PSL3.SmallCompletion.parabolicSL F false))
          (card_dvd_of_le (show Matrix.PSL3.LinearThree.borelSL F ≤
            Matrix.PSL3.SmallCompletion.parabolicSL F false from inf_le_left))
      apply hn.trans
      rw [Matrix.PSL3.SmallCompletion.card_parabolicSL,hF]
      decide
    omega
  | symplectic F hF b e =>
    have hp : Nat.card (overlap T X) = 2304 := by
      rw [Nat.card_congr e.some.middle.toEquiv,
        Theory.SpecificGroups.SymplecticFour.card_borel,hF]
      decide
    omega
  | g2 F hF b e => exact ⟨F,inferInstance,inferInstance,inferInstance,hF,b,e⟩

/-- No nonlinear original natural module fits any of the surviving full Borels. -/
theorem linear_of_fieldFour_comparison {c : Coordinates D S.field}
    {K₀ L₂ X : Subgroup G} (hX : IsCartan T L X) (hfour : S.field.degree = 2)
    (hc : FieldFourComparison T X K₀ L₂) :
    ∃ m, c = Coordinates.sl3 m := by
  have hle : Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) ≤ Nat.card (overlap T X) :=
    Nat.le_of_dvd (Nat.card_pos (α := overlap T X))
      (card_dvd_of_le ((innerSylow_le_commonTwo c hX).trans le_sup_left))
  have hu := hc.overlap_card_le
  cases c with
  | sl3 m => exact ⟨m,rfl⟩
  | sp4 m => have := sp4_innerSylow_large D S m hfour; omega
  | g2 m => have := g2_innerSylow_large D S m hfour; omega


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
