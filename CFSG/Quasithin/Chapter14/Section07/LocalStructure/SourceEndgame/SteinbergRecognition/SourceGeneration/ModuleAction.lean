module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.ModuleTransport
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
/-!
# The original Q-displacements in 14.7.72

The marked image equality Q*=R₁* from 14.7.66 transfers the upper
four-group calculation on the original U/V₁. The universal natural cover
identifies its moved and fixed spaces; the first equality in 14.7.65
identifies that fixed space with U₀V/V₁. The point containment proved in
14.7.70 lifts the equality back to the original subgroup commutator.

Source: Aschbacher–Smith, 14.7.65–66, the opening paragraph of the proof
of 14.7.70, and 14.7.72, printed pp.1070, 1073, 1075–1076.
-/
public section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SourceGeneration
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

private theorem image_membership (B : Subgroup G) (hZ : F.Vi 1 ≤ B) (x : F.U) :
    (d.conjugationSection.coordinates x).toAdd ∈ d.conjugationSection.imageSpace B ↔
      (x : G) ∈ B := by
  constructor
  · intro hx
    obtain ⟨b, hb, he⟩ := (d.conjugationSection.mem_imageSpace_iff B _).mp hx
    have hk : (x / b : F.U).val ∈ F.Vi 1 := by
      apply (d.conjugationSection.coordinates_eq_one_iff _).mp
      rw [map_div, Multiplicative.toAdd.injective he]
      exact div_self' _
    simpa using B.mul_mem (hZ hk) hb
  · intro hx
    exact (d.conjugationSection.mem_imageSpace_iff B _).mpr ⟨x, hx, rfl⟩

private def displacement (h : F.H) (a : F.U) : F.U :=
  (⟨h * a * (h : G)⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized h.property) a).mp a.property⟩ : F.U) * a⁻¹

private theorem displacement_coordinates (h : F.H) (a : F.U) :
    (d.conjugationSection.coordinates (displacement d h a)).toAdd =
      d.action h (d.conjugationSection.coordinates a).toAdd -
        (d.conjugationSection.coordinates a).toAdd := by
  rw [displacement, map_mul, map_inv]
  change (d.conjugationSection.coordinates _).toAdd +
    -(d.conjugationSection.coordinates a).toAdd = _
  rw [d.conjugationSection.equivariant, sub_eq_add_neg]

/-- The module computation uses the original star map and the same marked
upper subgroup as 14.7.65. Its premises contain no generation assertion
from 14.7.72. -/
theorem commutator_U_Q (c : CriticalPath (L := L) F)
    (images : c.EarlierImages) (hc : d.SectionCentralizer)
    (hmark : ((F.Ri L 1).subgroupOf F.H).map d.qH =
      (Matrix.SpecialLinearGroup.upperUnipotent SL2FourNatural.F).map
        (alternatingActor d.naturalQuotient))
    (h65 : SL2CentralExtension.upperFixed
      ((d.descendedAction hc).comp (alternatingActor d.naturalQuotient)) =
        d.conjugationSection.imageSpace (V ⊔ d.U₀))
    (hSQ : S F L ≤ Q T L)
    (hconj : ∃ l ∈ L, c.Uα = conjugate F.U l)
    (hpoint : F.Vi 1 ≤ ⁅F.U, c.Uα⁆) :
    ⁅F.U, Q T L⁆ = V ⊔ d.U₀ := by
  have hLQ : L ≤ normalizer (Q T L : Set G) :=
    le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hAQ : c.Uα ≤ Q T L := by
    obtain ⟨l, hl, he⟩ := hconj
    rw [he]
    exact (map_mono ((U_le_S (F := F) (L := L)).trans hSQ)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hLQ (L.inv_mem hl)))
  have hZ : F.Vi 1 ≤ ⁅F.U, Q T L⁆ :=
    hpoint.trans (commutator_mono le_rfl hAQ)
  have hQU : Q T L ≤ normalizer (F.U : Set G) :=
    (Q_le_H F).trans d.conjugationSection.normalized
  have hDU : ⁅F.U, Q T L⁆ ≤ F.U := le_normalizer_iff_commutator_le_left.mp hQU
  have hm : ((Q T L).subgroupOf F.H).map d.qH =
      (Matrix.SpecialLinearGroup.upperUnipotent SL2FourNatural.F).map
        (alternatingActor d.naturalQuotient) := by
    have he := congrArg (Subgroup.map d.model.toMonoidHom) images.image_eq
    have he' : ((Q T L).subgroupOf F.H).map d.qH =
        ((F.Ri L 1).subgroupOf F.H).map d.qH := by
      simpa only [CriticalFusion.Source.star, map_map, Data.qH] using he
    exact he'.trans hmark
  let M := SL2CentralExtension.movedSpace
    ((d.descendedAction hc).comp (alternatingActor d.naturalQuotient))
    (Matrix.SpecialLinearGroup.upperUnipotent SL2FourNatural.F) ⊤
  have hME : M = d.conjugationSection.imageSpace (V ⊔ d.U₀) :=
    (d.original_upper_moved_eq_fixed hc).trans h65
  have hMD : M ≤ d.conjugationSection.imageSpace ⁅F.U, Q T L⁆ := by
    apply iSup_le
    intro t
    have ht : alternatingActor d.naturalQuotient t ∈ ((Q T L).subgroupOf F.H).map d.qH := by
      rw [hm]
      exact mem_map_of_mem _ t.property
    obtain ⟨q, hq, he⟩ := ht
    rintro w ⟨v, rfl⟩
    have hv := d.conjugationSection.displacement_range_le_imageSpace_of_commutator_le
      (Q T L) ⁅F.U, Q T L⁆ (commutator_comm _ _).le q hq
    apply hv
    refine ⟨v, ?_⟩
    change d.action q v - v = d.descendedAction hc (alternatingActor d.naturalQuotient t) v - v
    rw [← he, d.descendedAction_apply]
  have hDE : ⁅F.U, Q T L⁆ ≤ V ⊔ d.U₀ := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro q hq a ha
    let qH : F.H := ⟨q, Q_le_H F hq⟩
    let aU : F.U := ⟨a, ha⟩
    have hq' : d.qH qH ∈ (Matrix.SpecialLinearGroup.upperUnipotent SL2FourNatural.F).map
        (alternatingActor d.naturalQuotient) := by
      rw [← hm]
      exact mem_map_of_mem _ hq
    obtain ⟨t, ht, he⟩ := hq'
    apply (image_membership d (V ⊔ d.U₀) ((F.le_seed 1).trans le_sup_left)
      (displacement d qH aU)).mp
    rw [← hME, displacement_coordinates, ← d.descendedAction_apply hc qH, ← he]
    apply Submodule.mem_iSup_of_mem (⟨t, ht⟩ : Matrix.SpecialLinearGroup.upperUnipotent SL2FourNatural.F)
    exact ⟨⟨(d.conjugationSection.coordinates aU).toAdd, Submodule.mem_top⟩, rfl⟩
  apply le_antisymm hDE
  intro x hx
  let a : F.U := ⟨x, sup_le (Data.V_le_U F) d.U₀_le_U hx⟩
  apply (image_membership d ⁅F.U, Q T L⁆ hZ a).mp
  apply hMD
  rw [hME]
  exact (d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨a, hx, rfl⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SourceGeneration
