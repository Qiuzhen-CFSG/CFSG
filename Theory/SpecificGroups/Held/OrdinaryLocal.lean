module
public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal
public import Theory.GroupTheory.DoubleCoverCentralizer.SylowCenterConjugacy

/-!
# Maximal two-central centralizers in Held

The marked max5 involution is central in a Sylow two-subgroup contained in
max5. Its certified centralizer is exactly max5, which is absolutely maximal.
The proved Sylow center order two and Sylow conjugacy transfer maximality
to every two-central involution. No simplicity or subgroup catalogue premise
is imposed on the concrete Held carrier.

This supplies the intrinsic maximality premise in the ordinary central-cover
argument for Aschbacher--Smith 15.1.20(3d), printed pp.1096--1097.
The ATLAS HeG1-max5W1 words, inversion conventions and source attribution
are retained in the imported calculation modules.
-/

public section
namespace Held.OrdinaryLocal
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
open TwoLocalCandidates

/-- Every two-central involution has an absolutely maximal centralizer. -/
theorem twoCentral_centralizer_isCoatom (t : He) (ht : orderOf t = 2)
    (hc : TwoCentral t) : IsCoatom (centralizer ({t} : Set He)) := by
  let z : He := max5First ^ 4
  obtain ⟨R,hR⟩ := RankOneLocalPair.exists_sylow_le_max5
  have hzC : z ∈ centralizer (R : Set He) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (CentralInvolutionBounds.max5_le_centralizer (hR hx))
  have hzR : z ∈ R := by
    have hh := centralizer_le_normalizer (R : Set He) hzC
    rwa [LocalPairs.SylowGeometry.Calculations.inner_self_normalizing R] at hh
  have hz : TwoCentral z := ⟨R,hzR,mem_center_iff.mpr (fun x => Subtype.ext (hzC x x.property))⟩
  apply hc.centralizer_isCoatom_of_center_card_two hz
    (fun he => by rw [he,orderOf_one] at ht; omega)
    (fun he => by
      have ho := CentralInvolutionBounds.orderOf_centralInvolution
      change orderOf z = 2 at ho
      rw [he,orderOf_one] at ho
      omega)
    LocalPairs.SylowGeometry.Calculations.inner_center_card
  rw [InvolutionFixedData.TwoB.centralizer_eq_max5]
  exact RankOneLocalPair.ConcreteMaximality.max5_isCoatom
end Held.OrdinaryLocal
