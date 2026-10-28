module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Criteria
public import CFSG.Quasithin.MainConverse.SporadicLocal.Janko3Reduction
public import Theory.SpecificGroups.Janko4.Model.OddLocalRanks
public import CFSG.Quasithin.MainConverse.SporadicLocal.J2
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3
public import CFSG.Quasithin.MainConverse.SporadicLocal.J4
public import CFSG.Quasithin.MainConverse.SporadicLocal.HS
public import CFSG.Quasithin.MainConverse.SporadicLocal.He
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru

/-!
# QT and even characteristic for J₂, J₃, J₄, HS, He and Ru

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(5), printed p.4, repeated as Theorem 0.1.1(5) on p.482.

The six imported model calculations prove QT and E for the exact carriers
in `ClassificationModels.SporadicName`. J₂, J₄, HS, He and Ru have global
odd prime rank at most two; J₃ instead uses an exhaustive cover of its
maximal two-locals. The even-characteristic proofs use intrinsic
self-centralizing two-cores and exhaustive local or Sylow-center arguments.

The assembly below transports these proved conclusions through actual group
isomorphisms. No extra local, order, simplicity or nonabelianness premise is
needed. Proper K remains the separate induction input to the classification.
The earlier conditional reduction APIs remain publicly available.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal

/-- The six non-Mathieu sporadic cases of QT and E in Theorem 0.1.2(5),
with every concrete model premise discharged. In particular this applies
to the finite nonabelian simple groups in the source theorem. -/
public theorem qt_e_of_six_sporadic_equiv
    {G : Type*} [Group G] [Finite G] {name : ClassificationModels.SporadicName}
    (hname : name = .j2 ∨ name = .j3 ∨ name = .j4 ∨
      name = .hs ∨ name = .he ∨ name = .ru)
    (e : G ≃* name.Carrier) : IsQuasithin G ∧ IsEvenCharacteristic G := by
  rcases hname with rfl | rfl | rfl | rfl | rfl | rfl
  · exact j2_qt_e_of_equiv e
  · exact j3_qt_e_of_equiv e
  · exact j4_qt_e_of_equiv e
  · exact hs_qt_e_of_equiv e
  · exact he_qt_e_of_catalogue_equiv e
  · exact ru_qt_e_of_equiv e

end CFSG.Quasithin.MainConverse.SporadicLocal
