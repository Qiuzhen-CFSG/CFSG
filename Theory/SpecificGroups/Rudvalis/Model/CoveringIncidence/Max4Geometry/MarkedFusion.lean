module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Basic
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.SylowPlacement
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.ElementaryEightParabolicRecognition

/-!
# Two-centrality of the marked Rudvalis eight-group

Place an ambient Sylow in max4. The normal marked eight-group belongs to it
and meets its center nontrivially. Full image of the max4 conjugation action,
together with transitivity of linear automorphisms on nonzero vectors, then
makes every nonidentity marked element two-central in the actual Rudvalis
model. Conjugation transports the actual Sylow-center witnesses.

This supplies the target class for the separate outside-core fusion
calculation of Aschbacher--Smith J.2.6(2), as consumed in I.2.2(7), printed
p.413. No global involution table is needed for this marked subgroup.
-/

namespace Rudvalis.CoveringIncidence
open Subgroup SylowOvergroups CoreQuotients
open SylowOvergroups.RadicalCoverage.LocalCover
open Theory.GroupTheory.DoubleCoverCentralizer
local instance : IsElementaryAbelian 2 (elementary 2) :=
  RankOneEightCharacteristic.elementary_two_elementary

public theorem exists_marked_twoCentral :
    ∃ x : elementary 2, x ≠ 1 ∧ TwoCentral (x : Model) := by
  obtain ⟨T, hT⟩ := max4ContainsSylow
  have hcore : max4Core ≤ T := by
    rintro x ⟨g, hg, rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hT) hg
  have hET : elementary 2 ≤ T := marked_eight_le_core.trans hcore
  let N := (elementary 2).subgroupOf T
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hET).mpr
    (hT.trans RankOneEightAction.max4_le_normalizer_eight)
  have hcard : Nat.card N = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hET).toEquiv).trans
      RankOneEightCharacteristic.elementary_two_card
  let : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨z, hz, hzc⟩ := exists_nontrivial_center_mem_normal (p := 2) N
  refine ⟨⟨(z : T), z.property⟩, ?_, T, (z : T).property, hzc⟩
  intro h
  have hv : ((z : T) : Model) = 1 := congrArg (fun a : elementary 2 => (a : Model)) h
  exact hz (Subtype.ext (Subtype.ext hv))

public theorem marked_eight_twoCentral (x : elementary 2) (hx : x ≠ 1) :
    TwoCentral (x : Model) := by
  obtain ⟨z, hz, hzc⟩ := exists_marked_twoCentral
  obtain ⟨a, ha⟩ := ElementaryEightParabolic.automorphism_transitive z x hz hx
  obtain ⟨g, rfl⟩ := max4EightAction_surjective a
  have he : MulAut.conj (g : Model) (z : Model) = (x : Model) :=
    congrArg Subtype.val ha
  rw [← he]
  exact hzc.map (MulAut.conj (g : Model))

public theorem twoCentral_of_conjugate_marked (g : Model) (x : elementary 2) (hx : x ≠ 1) :
    TwoCentral (g * (x : Model) * g⁻¹) :=
  (marked_eight_twoCentral x hx).map (MulAut.conj g)

end Rudvalis.CoveringIncidence
