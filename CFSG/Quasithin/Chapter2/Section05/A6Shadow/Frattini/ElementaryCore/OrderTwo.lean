module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.OrderTwo.Contained
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.OrderTwo.Lift
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.OrderTwo.Fusion
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.OrderTwo.Largest

/-!
# Order-two elementary-core orbit calculations

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 2.5.24, printed p.568.

If E₁ˣ lies in K S_C, the two elementary eight-groups in (S ∩ K)S_C
give the orbit through their relative centralizers. Otherwise fusion
constructs an actual centralizing involution upstairs. Adjoining it gives
the two local cores, which exhaust the largest elementary subgroups of S
and are conjugate in S. In both branches the orbit retains the original x.

The order-two reduction, z = z_K, the action clause of 2.5.22(1), and
the relative-centralizer formula remain explicit inputs for the source
assembly. No family or involution-lift premise remains in the orbit theorem.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable (d : EarlierSetup κ G)

/-- The contrary order-two branch: fusion supplies the actual involution,
and the complete elementary-sixteen family gives the original-x orbit. -/
theorem hasNormalizerOrbit_of_not_contained (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 2) (hz : d.z = d.zK) (hact : ZConjugateActions d)
    (hcore : ∀ E : Subgroup G, E ≤ d.S ⊓ d.K → IsKleinFour E →
      localCore d E = d.S ⊓ centralizer (E : Set G))
    (hout : ¬ rightConjugate d.x (fourZero d) ≤ d.K ⊔ d.SC) :
    HasNormalizerOrbit d := by
  obtain ⟨v⟩ := centralizingInvolution_of_not_contained d hEA hcard hz hact hout
  exact hasNormalizerOrbit_of_largest_pair d
    (largestElementary_eq_localCores d hEA hcard hcore v) (localCore_conjugate d hcore)

/-- Both order-two elementary-core branches of the 2.5.24 orbit argument,
with precisely the earlier action, reduction and local-core inputs. -/
theorem hasNormalizerOrbit_of_elementary_two (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 2) (hz : d.z = d.zK) (hact : ZConjugateActions d)
    (hcore : ∀ E : Subgroup G, E ≤ d.S ⊓ d.K → IsKleinFour E →
      localCore d E = d.S ⊓ centralizer (E : Set G)) :
    HasNormalizerOrbit d := by
  classical
  by_cases h : rightConjugate d.x (fourZero d) ≤ d.K ⊔ d.SC
  · exact hasNormalizerOrbit_of_contained d hEA hcard hz hcore h
  · exact hasNormalizerOrbit_of_not_contained d hEA hcard hz hact hcore h

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo
