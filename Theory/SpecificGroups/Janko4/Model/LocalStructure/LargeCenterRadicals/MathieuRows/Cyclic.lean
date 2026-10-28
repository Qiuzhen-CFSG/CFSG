module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.OctadSaturation
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativeSecond
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativeSecond

public import Theory.GroupTheory.PRadicalSylowNormalizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion

public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Excluding cyclic radical images in the native Mathieu local

Both involution classes have their whole centralizers in native local
stabilizers with larger normal two-subgroups: order sixteen in the octad
case and order sixty-four in the sextet case. Radical saturation rules out
an order-two radical. The actual J₄ image inherits radicality from the full
normalizer projection.

The internal `NativeSecond` import deliberately reuses its proved sextet
placement and transporter inside this proof; neither private name occurs in
the public interface. This avoids changing or duplicating its fixed-octad
partition calculation. Source: An--O'Brien--Wilson (2003), §4 and Table 1,
pp.122,124; the native centralizer placement proves Aschbacher (1994), 41.2.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
open Sporadic.Mathieu M24LocalGeometry M24InvolutionCentralizers

private theorem radical_card_bound_of_normalizer_le (A D : Subgroup M24)
    (hA : A.IsPRadical 2) (hN : normalizer (A : Set M24) ≤ D) :
    Nat.card (pCore 2 D) ≤ Nat.card A := by
  have hc : D.pCoreIn 2 ≤ A :=
    le_of_normalizer_le_normalizer_of_pCore_normalizer_le A _ hA.isPGroup
      (isPGroup_pCoreIn 2 _) hA.2.le
      (hN.trans (D.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 D))))
  have h := card_le_of_le hc
  simpa only [pCoreIn,card_map_of_injective D.subtype_injective] using h

private theorem second_centralizer_placement : ∃ g : M24,
    centralizer2B.map (MulAut.conj g).toMonoidHom ≤ sextetStabilizer standardSextet := by
  exact ⟨Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource.NativeSecond.transporter,
    Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource.NativeSecond.centralizer_sextet_placement⟩

/-- No order-two subgroup of the actual Mathieu group is two-radical. -/
theorem radical_image_card_ne_two (A : Subgroup M24) (hA : A.IsPRadical 2) :
    Nat.card A ≠ 2 := by
  intro hcard
  obtain ⟨x,hx,hx1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have hxord : orderOf x = 2 := by
    have hd := orderOf_dvd_natCard (⟨x,hx⟩ : A)
    rw [orderOf_mk,hcard] at hd
    exact (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left (by
      simpa only [orderOf_eq_one_iff] using hx1)
  have he : A = zpowers x := (eq_of_le_of_card_ge (zpowers_le.mpr hx) (by
    rw [Nat.card_zpowers,hxord,hcard])).symm
  have hN : normalizer (A : Set M24) = centralizer ({x} : Set M24) := by
    rw [he]
    exact normalizer_zpowers_eq_centralizer_of_order_two x hxord
  rcases involution_classes x hxord with ha | hb
  · obtain ⟨g,hg⟩ := isConj_iff.mp ha.symm
    let c := MulAut.conj g
    have hn : normalizer (A.map c.toMonoidHom : Set M24) = centralizer2A := by
      rw [← map_equiv_normalizer_eq,hN,map_centralizer_equiv,Set.image_singleton]
      exact congrArg (fun z : M24 => centralizer ({z} : Set M24)) hg
    have hh := radical_card_bound_of_normalizer_le (A.map c.toMonoidHom)
      (octadStabilizer TwoA.fixedOctad) (hA.map_equiv c)
      (hn ▸ TwoA.centralizer_le_octad)
    rw [card_map_of_injective c.injective,hcard,
      M24ChapterHStabilizers.OctadAction.core_card] at hh
    omega
  · obtain ⟨g,hg⟩ := isConj_iff.mp hb.symm
    let c := MulAut.conj g
    have hn : normalizer (A.map c.toMonoidHom : Set M24) = centralizer2B := by
      rw [← map_equiv_normalizer_eq,hN,map_centralizer_equiv,Set.image_singleton]
      exact congrArg (fun z : M24 => centralizer ({z} : Set M24)) hg
    obtain ⟨k,hk⟩ := second_centralizer_placement
    let d := MulAut.conj k
    have hnd : normalizer ((A.map c.toMonoidHom).map d.toMonoidHom : Set M24) ≤
        sextetStabilizer standardSextet := by
      rw [← map_equiv_normalizer_eq,hn]
      exact hk
    have hh := radical_card_bound_of_normalizer_le _ _
      ((hA.map_equiv c).map_equiv d) hnd
    rw [card_map_of_injective d.injective,card_map_of_injective c.injective,hcard,
      SextetCore.core_card] at hh
    omega
/-- The literal image of a radical whose whole normalizer lies in max1
cannot be cyclic of order two. -/
theorem native_radical_image_card_ne_two (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ ElementaryNormalizerCover.max1) :
    Nat.card ((P.subgroupOf ElementaryNormalizerCover.max1).map
      MathieuHallActors.projection) ≠ 2 := by
  intro hc
  have hn : (P.subgroupOf ElementaryNormalizerCover.max1).map
      MathieuHallActors.projection ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hc
    omega
  exact radical_image_card_ne_two _ ⟨hn,radical_image_core P hP hN⟩ hc

end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
