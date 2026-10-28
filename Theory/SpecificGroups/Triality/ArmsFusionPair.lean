module
public import Theory.SpecificGroups.Triality.ArmsFixedQuotient

/-!
# A centralizing root pair in the triality arms radical

The positive long roots at positions 3 and 10 commute with the short-root
orbit at positions 7, 8 and 9. Their commutator is the highest root at
position 11. The actual radical coordinate multiplication proves all three
identities for symbolic field parameters, including q=2, without a new
finite certificate. This supplies the local pair in Aschbacher--Smith
F.4.35, printed p.292. FusionWitness transports it to the original core.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
open Parabolics RadicalCoordinates RadicalCoordinates.Centers RadicalCoordinates.LeviCommutators

private theorem coordinates_commutator (P : Parameters) (hp : P.prime=2)
    (v w : ArmsParameters P) :
    ⁅armsCoordinates P hp v,armsCoordinates P hp w⁆ =
      armsCoordinates P hp (centralParameters P (armsCommutator P v w)) := by
  let f := MulEquiv.subgroupCongr (radical_eq_descendedRootSubgroup P hp .arms).symm
  exact (map_commutatorElement f.toMonoidHom _ _).symm.trans
    (congrArg f (armsEquiv_commutator P hp v w))

/-- The two lower long roots centralize the highest short-root group and
have commutator equal to the highest long root. All elements lie in the
actual first radical. -/
theorem higher_short_root_pair (P : Parameters) (hp : P.prime=2) (d : ExtensionField P) (z : fixedField P) :
    long P hp 0 z∈radical P .arms ∧ long P hp 1 1∈radical P .arms ∧
    Commute (long P hp 0 z) (short P hp 2 d) ∧
    Commute (long P hp 1 1) (short P hp 2 d) ∧
    ⁅long P hp 0 z,long P hp 1 1⁆=highestHom P hp (Multiplicative.ofAdd z) := by
  have hv (b e f : fixedField P) (d : ExtensionField P) :
      (armsCoordinates P hp (![0,d],![b,e,f])).val=
        long P hp 0 b*short P hp 2 d*long P hp 1 e*long P hp 2 f := by
    rw [armsCoordinates_factorization]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,short_zero,mul_one]
  have hc (v w : ArmsParameters P) :
      ⁅(armsCoordinates P hp v).val,(armsCoordinates P hp w).val⁆=
        (armsCoordinates P hp (centralParameters P (armsCommutator P v w))).val :=
    congrArg Subtype.val (coordinates_commutator P hp v w)
  have hcomm (b e : fixedField P) :
      Commute (long P hp 0 b*long P hp 1 e) (short P hp 2 d) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hh := hc (![0,0],![b,e,0]) (![0,d],![0,0,0])
    have hz : armsCommutator P (![0,0],![b,e,0]) (![0,d],![0,0,0])=0 := by
      simp [armsCommutator,armsCocycle]
    have he : (armsCoordinates P hp (centralParameters P 0)).val=1 :=
      (armsEquiv_centralParameters P hp 0).trans (map_one (highestHom P hp))
    rw [hz,he] at hh
    simpa only [hv,short_zero,long_zero,mul_one,one_mul] using hh
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [radical_eq_descendedRootSubgroup P hp .arms]
    exact long_mem P hp .arms 0 trivial z
  · rw [radical_eq_descendedRootSubgroup P hp .arms]
    exact long_mem P hp .arms 1 trivial 1
  · simpa only [long_zero,mul_one] using hcomm z 0
  · simpa only [long_zero,one_mul] using hcomm 0 1
  · have hh := hc (![0,0],![z,0,0]) (![0,0],![0,1,0])
    have hz : armsCommutator P (![0,0],![z,0,0]) (![0,0],![0,1,0])=z := by
      simp [armsCommutator,armsCocycle]
    rw [hz] at hh
    have he : (armsCoordinates P hp (centralParameters P z)).val=
        highestHom P hp (Multiplicative.ofAdd z) := armsEquiv_centralParameters P hp z
    rw [he] at hh
    simpa only [hv,short_zero,long_zero,mul_one,one_mul] using hh

end Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
