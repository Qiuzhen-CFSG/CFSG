module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Three.OneCentralizer.Checks
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Base
public import Theory.GroupTheory.GeneratorCosetCoverIndex

/-!
# Coverage in the first literal cubic centralizer of the Hall--Janko carrier

The 560 certified distinct conjugates of representative 1 give a lower bound on
its centralizer index. Since the carrier has order 604800, the centralizer has
at most 1080 elements. The 1080 certified distinct commuting normal forms are
therefore exhaustive. Each has a checked carrier conjugator from one of the
21 designated representatives. This proves coverage for the entire centralizer,
including mixed orders such as 15, and supplies the odd-order cubic premise
needed by `covered_odd_of_three_dvd_of_centralizers` in `Coverage.Three`.

Source: the retained ATLAS `J2G1-p100B0` generators and certified normal forms.
The adjacent `OneCentralizer/source/README.md` records provenance, conventions,
and reproduction. External computations only find witnesses; all cardinality
bounds, completeness and conjugation assertions are proved here.
-/

namespace Sporadic.LeechRelated.J2.PowerFusionCertificate
open OneCentralizerCertificates

private abbrev cubicCentralizer : Subgroup Carrier :=
  Subgroup.centralizer ({representative 1} : Set Carrier)

private def centralElement (i : Fin 1080) : Carrier := element (centralIndex i)
private def orbitElement (i : Fin 560) : Carrier := element (orbitIndex i)
private def cosetRepresentative (i : Fin 560) : Carrier := element (rightRepresentative i)

private theorem centralElement_mem (i : Fin 1080) : centralElement i ∈ cubicCentralizer := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply carrier_ext_base
  exact commute_check i

private theorem centralElement_injective : Function.Injective centralElement := by
  intro i j h
  exact centralIndex_injective
    (ExceptionalParabolics.FirstParabolic.normalForm_injective (congrArg inclusion h))

private theorem orbitElement_injective : Function.Injective orbitElement := by
  intro i j h
  exact orbitIndex_injective
    (ExceptionalParabolics.FirstParabolic.normalForm_injective (congrArg inclusion h))

private theorem cosetRepresentative_spec (i : Fin 560) :
    representative 1 * cosetRepresentative i = cosetRepresentative i * orbitElement i := by
  apply carrier_ext_base
  exact orbit_check i

private theorem conjugate_spec (i : Fin 560) :
    (cosetRepresentative i)⁻¹ * representative 1 * cosetRepresentative i = orbitElement i := by
  rw [mul_assoc, cosetRepresentative_spec, inv_mul_cancel_left]

private theorem coset_separation (i j : Fin 560)
    (h : cosetRepresentative i * (cosetRepresentative j)⁻¹ ∈ cubicCentralizer) : i = j := by
  have hc := Subgroup.mem_centralizer_singleton_iff.mp h
  have he := congrArg
    (fun z : Carrier => (cosetRepresentative i)⁻¹ * z * cosetRepresentative j) hc
  have hv : (cosetRepresentative j)⁻¹ * representative 1 * cosetRepresentative j =
      (cosetRepresentative i)⁻¹ * representative 1 * cosetRepresentative i := by
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      inv_mul_cancel, mul_inv_cancel, one_mul, mul_one] using he
  rw [conjugate_spec, conjugate_spec] at hv
  exact orbitElement_injective hv.symm

private theorem centralizer_index_lower : 560 ≤ cubicCentralizer.index := by
  simpa only [Nat.card_fin] using
    Subgroup.card_le_index_of_rightCoset_separation cubicCentralizer
      cosetRepresentative coset_separation

private theorem centralizer_card_upper : Nat.card cubicCentralizer ≤ 1080 := by
  have hcard := cubicCentralizer.card_mul_index
  rw [ExceptionalParabolics.FirstParabolic.card_carrier] at hcard
  have h := Nat.mul_le_mul_left (Nat.card cubicCentralizer) centralizer_index_lower
  rw [hcard] at h
  exact le_of_mul_le_mul_right
    (show Nat.card cubicCentralizer * 560 ≤ 1080 * 560 from h) (by decide : 0 < 560)

private def centralizerEntry (i : Fin 1080) : cubicCentralizer :=
  ⟨centralElement i, centralElement_mem i⟩

private theorem centralizerEntry_surjective : Function.Surjective centralizerEntry := by
  have hinj : Function.Injective centralizerEntry := by
    intro i j h
    exact centralElement_injective (congrArg Subtype.val h)
  exact (hinj.bijective_of_nat_card_le
    (by simpa only [Nat.card_fin] using centralizer_card_upper)).2

private theorem centralElement_fusion (i : Fin 1080) :
    IsConj (representative (fusionClass i)) (centralElement i) := by
  apply isConj_of_base _ _ (element (fusionConjugator i))
  exact fusion_check i

/-- Every element of the full first cubic centralizer is conjugate, inside the
literal Hall--Janko carrier, to one of the 21 designated representatives. -/
public theorem covered_three_centralizer_one (g : Carrier)
    (hg : g ∈ Subgroup.centralizer ({representative 1} : Set Carrier)) :
    ∃ i : Fin 21, IsConj (representative i) g := by
  obtain ⟨j, hj⟩ := centralizerEntry_surjective ⟨g, hg⟩
  have he : centralElement j = g := congrArg Subtype.val hj
  exact ⟨fusionClass j, he ▸ centralElement_fusion j⟩

/-- The first centralizer premise of the odd cubic coverage reduction, including
composite orders. The full-centralizer certificate requires no order restriction. -/
public theorem covered_odd_three_centralizer_one (g : Carrier)
    (hg : g ∈ Subgroup.centralizer ({representative 1} : Set Carrier))
    (_h2 : ¬2 ∣ orderOf g) (_h3 : 3 ∣ orderOf g) :
    ∃ i : Fin 21, IsConj (representative i) g :=
  covered_three_centralizer_one g hg

end Sporadic.LeechRelated.J2.PowerFusionCertificate
