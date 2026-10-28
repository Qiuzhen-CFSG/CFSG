module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.FourGeometry
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.PlaneCentralizer.Definitions
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.CentralizerSylow

/-!
# Bounding the full ambient plane centralizer by a single orbit

The marking sends the two plane generators to the original max2 words
`sourceP` and `t`. Thus conjugation injects the full ambient plane centralizer
into the centralizer of `sourceP` in the certified group C(t). A family of
1386 distinct conjugates gives disjoint translates of that singleton centralizer;
its order is consequently at most 21799895040 / 1386 = 15728640.

Both the marking and the finite orbit certificate remain explicit here. The
third marking equation is unused. Source context: Aschbacher--Smith A.3.12,
pp.47--48; Kleidman--Wilson (1988), pp.484--510; retained ATLAS max2 provenance.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
open Subgroup Janko4 Janko4.LocalStructure.SymmetricLinear
open Janko4.LocalStructure.SymmetricLinear.NormalEight
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup

namespace PlaneCentralizer
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open Max4EightCentralizer

private theorem source_eq_centralizer : sourceSubgroup = centralizer ({t} : Set Model) := by
  have hmap : sourceSubgroup.map (MulAut.conj h⁻¹).toMonoidHom =
      centralizer ({a} : Set Model) := by
    rw [sourceSubgroup_map_conj, localSubgroup_eq_top, ← MonoidHom.range_eq_map,
      centralizerToModel_range]
  ext g
  have hm : g ∈ sourceSubgroup ↔ (MulAut.conj h⁻¹) g ∈
      centralizer ({a} : Set Model) := by
    rw [← hmap]
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [hm, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  have ht : (MulAut.conj h⁻¹) t = a := by
    simpa only [MulAut.conj_apply, inv_inv] using conjugates_t
  rw [← ht, ← map_mul, ← map_mul]
  exact (MulAut.conj h⁻¹).injective.eq_iff

private theorem source_card : Nat.card sourceSubgroup = 21799895040 := by
  rw [card_sourceSubgroup_eq_localSubgroup, localSubgroup_eq_top, card_top]
  exact Janko4.OuterReduction.OddIndex.centralizer_card

private abbrev singleCentralizer : Subgroup sourceSubgroup :=
  centralizer ({sourceP} : Set sourceSubgroup)

private theorem singleOrbit_mul (g : sourceSubgroup) (c : singleCentralizer) :
    (MulAut.conj (g * (c : sourceSubgroup))) sourceP = (MulAut.conj g) sourceP := by
  have hp := c.property sourceP (by simp)
  have hf : (MulAut.conj (c : sourceSubgroup)) sourceP = sourceP := by
    simp only [MulAut.conj_apply, ← hp, mul_inv_cancel_right]
  rw [map_mul]
  change (MulAut.conj g) ((MulAut.conj (c : sourceSubgroup)) sourceP) = _
  rw [hf]

private theorem singleCentralizer_card_le (ho : SingleOrbitWitness) :
    Nat.card singleCentralizer ≤ 15728640 := by
  obtain ⟨w, hw⟩ := ho
  let f : Fin 1386 × singleCentralizer → sourceSubgroup := fun x => w x.1 * x.2
  have hf : Function.Injective f := by
    rintro ⟨i, c⟩ ⟨j, d⟩ hij
    have he : i = j := hw (by
      simpa only [f, singleOrbit_mul] using
        congrArg (fun g => (MulAut.conj g) sourceP) hij)
    subst j
    have hcd : c = d := Subtype.ext (mul_left_cancel hij)
    subst d
    rfl
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_fin, source_card] at hc
  omega

private theorem planeElement_mem (i : Fin 4) : (element (planeIndex i) : Model) ∈ max4Plane :=
  mem_map_of_mem _ (show element (planeIndex i) ∈ localPlane from ⟨i, rfl⟩)

private theorem conjugate_commute_of_marking (hm : Marking)
    (c : centralizer (max4Plane : Set Model)) :
    let z := (MulAut.conj bridge) (c : Model)
    z * t = t * z ∧ z * (sourceP : Model) = sourceP * z := by
  have hc (i : Fin 4) :
      (MulAut.conj bridge) (c : Model) * (MulAut.conj bridge) (element (planeIndex i) : Model) =
      (MulAut.conj bridge) (element (planeIndex i) : Model) * (MulAut.conj bridge) (c : Model) := by
    simpa only [map_mul] using
      congrArg (MulAut.conj bridge) (c.property _ (planeElement_mem i)).symm
  exact ⟨hm.2.1 ▸ hc 2, hm.1 ▸ hc 1⟩

/-- The first two marking equations place the entire ambient plane centralizer
in the source singleton centralizer. The 1386 actual conjugates bound its order. -/
theorem centralizer_card_le_of_marking_and_orbit (hm : Marking) (ho : SingleOrbitWitness) :
    Nat.card (centralizer (max4Plane : Set Model)) ≤ 15728640 := by
  let f : centralizer (max4Plane : Set Model) → singleCentralizer := fun c =>
    ⟨⟨(MulAut.conj bridge) (c : Model), by
      rw [source_eq_centralizer, mem_centralizer_singleton_iff]
      exact (conjugate_commute_of_marking hm c).1⟩, by
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (conjugate_commute_of_marking hm c).2⟩
  have hf : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    apply (MulAut.conj bridge).injective
    exact congrArg (fun x : singleCentralizer => ((x : sourceSubgroup) : Model)) he
  exact (Nat.card_le_card_of_injective f hf).trans (singleCentralizer_card_le ho)

end PlaneCentralizer
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
