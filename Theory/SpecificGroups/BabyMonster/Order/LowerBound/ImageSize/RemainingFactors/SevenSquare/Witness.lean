module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.SevenSquare.Witness.Contract

/-!
# Assembly of the concrete seven-square grid

The two group words belong to the fixed standard subgroup by construction.
The fourteen packed vectors have pairwise distinct sums, checked in `Vectors`.
The remaining concrete calculation consists of the 28 vector transitions
recorded by `Concrete.Transitions`. Given those checked transitions, this module
assembles the exact `GridCertificate`; it does not infer transitions from the
untrusted search or from an abstract identification of the local subgroup.
-/

@[expose] public section
namespace BabyMonster.OrderLowerBound.RemainingFactors.SevenSquare

open LargePrimes

/-- Final assembly, conditional only on the explicitly recorded evaluations. -/
theorem seven_grid_of_transitions (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (h : Concrete.Transitions ha hb) : Nonempty (GridCertificate ha hb) := by
  refine ⟨GridCertificate.ofTwoCycles
    (Concrete.candidatePair ha hb).1.val (Concrete.candidatePair ha hb).2.val
    (Concrete.candidatePair ha hb).1.property (Concrete.candidatePair ha hb).2.property
    (fun i => vector (Concrete.u i)) (fun j => vector (Concrete.w j)) ?_
    h.xu h.xw h.yu h.yw⟩
  intro p q hpq
  by_contra hne
  obtain ⟨k, hk⟩ := Concrete.separates p q hne
  apply hk
  change vector (Concrete.u p.1 ^^^ Concrete.w p.2) k =
    vector (Concrete.u q.1 ^^^ Concrete.w q.2) k
  rw [packedVector_xor, packedVector_xor]
  exact congrFun hpq k

end BabyMonster.OrderLowerBound.RemainingFactors.SevenSquare
