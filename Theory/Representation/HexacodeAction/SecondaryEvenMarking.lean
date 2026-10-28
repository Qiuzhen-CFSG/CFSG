module

public import Theory.Representation.HexacodeAction.SecondaryEquality
public import Theory.Representation.BinaryDuadStructure.OppositeCover.Geometry
-- Internal continuation of the frozen Sylow calculation: its concrete words
-- have private bodies, used only to certify the exact coordinate marking.
import all Theory.Representation.HexacodeAction.ThompsonOffenders

/-!
# The even equality offender selects the original secondary marking

The hexacode's even offender is conjugate to its plane four-group. In the
literal six-coordinate quotient this is the even matching group. It fixes
only the base syntheme, so the second natural module has fixed codimension
at least three there. Thus an actual secondary fixed-codimension-two actor
cannot select the diagram-twisted natural model, even in the equality case.

Source: Aschbacher--Smith 12.7.20, printed p.846.
-/

public section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes
open Theory.SpecificGroups.SymmetricSix BinaryDuadModule BinaryAlternatingSix
open Hexacode.ThompsonOffenders BinaryDuadStructure.OppositeCover
namespace Representation.Hexacode.SecondaryEvenMarking

private abbrev q := hexCoordinateSixHom.comp hexSign.ker.subtype

private theorem point_action (g : S6) (s : Syntheme) :
    secondNatural g (polarVector (linePoint s)).val =
      (polarVector (linePoint (synthemeAct g s))).val := by
  change polarAction (diagramAut g) (polarVector (linePoint s)).val = _
  rw [polarAction_vector, ← linePoint_equivariant]

private theorem matching_fixed (s : Syntheme) :
    synthemeAct (q SylowModel.z) s = s ∧ synthemeAct (q SylowModel.t) s = s ↔ s = 0 := by
  have hz : q SylowModel.z = Equiv.swap 0 1 * Equiv.swap 2 3 := by simp [q,SylowModel.z]
  have ht : q SylowModel.t = Equiv.swap 0 1 * Equiv.swap 4 5 := by simp [q,SylowModel.t]
  rw [hz,ht]
  simp only [← synthemePartition_injective.eq_iff, synthemePartition_act]
  fin_cases s <;> decide

private theorem plane_cost :
    3 ≤ fixedCodim (secondNatural.comp q) SylowModel.planeGroup := by
  have hfix : fixedSpace (secondNatural.comp q) SylowModel.planeGroup ≤
      Submodule.span (ZMod 2) {(polarVector (linePoint 0)).val} := by
    intro v hv
    by_cases hv0 : v = 0
    · simpa only [hv0] using (Submodule.zero_mem (Submodule.span (ZMod 2) {(polarVector (linePoint 0)).val}))
    obtain ⟨d,hd⟩ := polarVector_bijective.2 ⟨v,hv0⟩
    obtain ⟨s,rfl⟩ := linePoint.surjective d
    have he : (polarVector (linePoint s)).val = v := congrArg Subtype.val hd
    have hz : secondNatural (q SylowModel.z) v = v := hv ⟨SylowModel.z,by
      exact ⟨(1,0),by simp [SylowModel.planeWord,SylowModel.word]⟩⟩
    have ht : secondNatural (q SylowModel.t) v = v := hv ⟨SylowModel.t,by
      exact ⟨(0,1),by simp [SylowModel.planeWord,SylowModel.word]⟩⟩
    rw [←he,point_action] at hz ht
    have hs : s = 0 := (matching_fixed s).mp ⟨
      linePoint.injective (polarVector_injective (Subtype.ext hz)),
      linePoint.injective (polarVector_injective (Subtype.ext ht))⟩
    rw [←he,hs]
    exact Submodule.subset_span (Set.mem_singleton _)
  have hdim := Submodule.finrank_mono hfix
  rw [finrank_span_singleton (polarVector (linePoint 0)).property] at hdim
  have hc := fixedCodim_add_finrank (secondNatural.comp q) SylowModel.planeGroup
  rw [naturalModule_finrank] at hc
  omega

/-- Every genuine even hexacode offender costs at least three dimensions on
its literal coordinate image in the second natural module. -/
theorem even_offender_second_cost (A : Subgroup HexEvenAutomorphisms)
    (hA : IsOffender evenAction A) :
    3 ≤ fixedCodim secondNatural (A.map (hexCoordinateSixHom.comp hexSign.ker.subtype)) := by
  have hb := hA.isBest_of_not_strong evenAction no_strong
  obtain ⟨S,hAS⟩ := hA.1.2.isPGroup.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq HexEvenAutomorphisms S standardSylow
  have hS : (S : Subgroup HexEvenAutomorphisms).map (MulAut.conj g).toMonoidHom =
      SylowModel.sylowGroup := congrArg Sylow.toSubgroup hg
  let B := A.map (MulAut.conj g).toMonoidHom
  have hB := hb.map_conj evenAction g
  have hBS : B ≤ SylowModel.sylowGroup := by
    rw [←hS]
    exact Subgroup.map_mono hAS
  have hcard : Nat.card B = 4 := (bestOffender_dimensions B hB).2.1
  have hplane : B = SylowModel.planeGroup := by
    rcases SylowModel.fourGroup_exhaustion B hB.1.2 hBS hcard with he | he
    · exact (lineGroup_not_offender (he ▸ hB.isOffender _)).elim
    · exact he
  have hc := fixedCodim_map_conj (secondNatural.comp q) A g
  change fixedCodim (secondNatural.comp q) B = _ at hc
  rw [hplane] at hc
  have hcost : 3 ≤ fixedCodim (secondNatural.comp q) A := hc ▸ plane_cost
  unfold fixedCodim at hcost ⊢
  rwa [fixedSpace_comp_map] at hcost

/-- The full-group version retains the original cover and literal coordinate
homomorphism, rather than identifying the secondary action up to automorphism. -/
theorem full_even_offender_second_cost (A : Subgroup HexAutomorphisms)
    (he : A ≤ hexSign.ker) (hA : IsOffender action A) :
    3 ≤ fixedCodim secondNatural (A.map hexCoordinateSixHom) := by
  let B := A.subgroupOf hexSign.ker
  let : IsElementaryAbelian 2 A := hA.1.2
  have hB : IsOffender evenAction B := by
    have hmap : B.map hexSign.ker.subtype = A := map_subgroupOf_eq_of_le he
    have hBE : IsElementaryTwo B := by
      refine ⟨?_,IsElementaryAbelian.subgroupOf he⟩
      intro hz
      apply hA.1.1
      rw [←hmap,hz,Subgroup.map_bot]
    have hr : rank B = rank A := by
      rw [←hmap,rank_map_injective _ Subtype.val_injective]
    refine ⟨hBE,?_⟩
    have hc : fixedCodim evenAction B = fixedCodim action A := by
      change fixedCodim (action.comp hexSign.ker.subtype) B = _
      unfold fixedCodim
      rw [fixedSpace_comp_map,hmap]
    rw [hc,hr]
    exact hA.2
  have hh := even_offender_second_cost B hB
  simpa only [←map_map,B,map_subgroupOf_eq_of_le he] using hh

end Representation.Hexacode.SecondaryEvenMarking
