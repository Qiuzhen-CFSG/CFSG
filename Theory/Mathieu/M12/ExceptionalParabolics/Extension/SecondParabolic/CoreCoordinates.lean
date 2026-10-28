module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.Core

/-!
# Explicit coordinates for the embedded second two-core

The two-core is the centralizer of the natural four in the whole overlap.
Its coordinates are exactly the 64 whole-overlap coordinates commuting with
the marked paired quaternion generator. The coordinate equivalence below
retains the actual inclusion in the fixed degree-24 permutation carrier.
This specifies the core independently of either the quaternion-swap subgroup
or the first parabolic's two-core.
Source: Aschbacher--Smith, F.1.12(I)(13), p.263, and 14.2.21, p.988.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
open QuaternionSwapModel MarkedSylow
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def naturalCoordinate : Coordinates := ((QuaternionGroup.xa 0,2,false),false)

theorem evaluate_naturalCoordinate (m : InnerModel) : (geometry m).evaluate naturalCoordinate = v := by
  change rawValue (raw naturalCoordinate.1) * 1 = v
  rw [mul_one]
  decide +kernel

theorem secondCore_image_in_overlap (m : InnerModel) :
    (pCore 2 secondParabolic).map secondParabolic.subtype =
      overlap ⊓ Subgroup.centralizer ({v} : Set Carrier) := by
  rw [secondCore_image m]
  ext g
  constructor
  · intro hg
    have hz : g ∈ firstParabolic := Subgroup.mem_centralizer_singleton_iff.mpr
      (hg z (Subgroup.subset_closure (by simp))).symm
    have hv : g ∈ Subgroup.centralizer ({v} : Set Carrier) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hg v (Subgroup.subset_closure (by simp))).symm
    exact ⟨⟨hz,Subgroup.centralizer_le_normalizer _ hg⟩,hv⟩
  · rintro ⟨hg,hv⟩
    rw [natural,Subgroup.centralizer_closure]
    rintro x (rfl | rfl)
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hg.1).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hv).symm

def SecondCoreCoordinates := {n : Coordinates // Commutes n naturalCoordinate}

instance : Fintype SecondCoreCoordinates := inferInstanceAs (Fintype {n : Coordinates // Commutes n naturalCoordinate})

theorem card_secondCoreCoordinates : Fintype.card SecondCoreCoordinates = 64 := by decide +kernel

theorem evaluate_mem_secondCore (m : InnerModel) (n : Coordinates) :
    (geometry m).evaluate n ∈ (pCore 2 secondParabolic).map secondParabolic.subtype ↔
      Commutes n naturalCoordinate := by
  rw [secondCore_image_in_overlap m]
  constructor
  · intro h
    apply ((geometry m).evaluate_commute n naturalCoordinate).mp
    rw [evaluate_naturalCoordinate]
    exact Subgroup.mem_centralizer_singleton_iff.mp h.2
  · intro h
    refine ⟨((geometry m).evaluate_cover _).mpr ⟨n,rfl⟩, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← evaluate_naturalCoordinate m]
    exact ((geometry m).evaluate_commute n naturalCoordinate).mpr h

def secondCoreElement (m : InnerModel) (n : SecondCoreCoordinates) : pCore 2 secondParabolic :=
  ⟨⟨(geometry m).evaluate n.val, (((geometry m).evaluate_cover _).mpr ⟨n.val,rfl⟩).2⟩,
    (secondCore_mem_iff m _).mpr (by
      rw [← secondCore_image m]
      exact (evaluate_mem_secondCore m n.val).mpr n.property)⟩

theorem secondCoreElement_bijective (m : InnerModel) : Function.Bijective (secondCoreElement m) := by
  constructor
  · intro a b h
    apply Subtype.ext
    apply (geometry m).evaluate_injective
    exact congrArg (fun x : pCore 2 secondParabolic => (x.val : Carrier)) h
  · intro g
    have hg : (g.val : Carrier) ∈ (pCore 2 secondParabolic).map secondParabolic.subtype :=
      ⟨g.val,g.property,rfl⟩
    have ht : (g.val : Carrier) ∈ overlap := by
      rw [secondCore_image_in_overlap m] at hg
      exact hg.1
    obtain ⟨n,hn⟩ := ((geometry m).evaluate_cover _).mp ht
    have hc : Commutes n naturalCoordinate := (evaluate_mem_secondCore m n).mp (hn.symm ▸ hg)
    refine ⟨⟨n,hc⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hn

def secondCoreCoordinateEquiv (m : InnerModel) : SecondCoreCoordinates ≃ pCore 2 secondParabolic :=
  Equiv.ofBijective (secondCoreElement m) (secondCoreElement_bijective m)

theorem secondCoreCoordinateEquiv_apply (m : InnerModel) (n : SecondCoreCoordinates) :
    ((secondCoreCoordinateEquiv m n).val : Carrier) = (geometry m).evaluate n.val := rfl

end Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
