module

public import CFSG.Quasithin.ChapterA.Section01.Linear.Dickson
public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer

/-!
# Linear group inputs to Appendix A.1

The corrected Dickson classification A.1.3 is proved in `Linear.Dickson`.
The Singer-overgroup theorem A.1.12 is proved in `Linear.Singer`: a cyclic
group acting regularly on the nonzero vectors of a binary space is normal
in every odd-order overgroup. Regularity means the actual free and
transitive action, with all primitive-prime and dimension-six inputs proved.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.3 and A.1.12, printed pp.20 and 22.
-/

namespace CFSG.Quasithin.ChapterA

/-- A.1.12: an odd-order overgroup of a regular cyclic binary linear group
normalizes that cyclic group. -/
public theorem lemma_A_1_12
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (X Y : Subgroup (V ≃ₗ[ZMod 2] V))
    (hcyc : IsCyclic X) (hreg : LinearGroup.IsRegularOnNonzero X)
    (hXY : X ≤ Y) (hodd : Odd (Nat.card Y)) : (X.subgroupOf Y).Normal :=
  Singer.normal_of_odd X Y hcyc hreg hXY hodd

end CFSG.Quasithin.ChapterA
