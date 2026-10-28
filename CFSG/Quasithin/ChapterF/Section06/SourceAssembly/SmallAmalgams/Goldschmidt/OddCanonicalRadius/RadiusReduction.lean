module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddCanonicalRadius.Transforms
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Reversing the odd-radius source commutator

The source commutator fixes the label four steps to the right of its first
center. Reverse the track and translate that identity to interchange the two
original centers. Its commutator is the inverse of the original involution,
so the two resulting midpoint labels coincide. Their exact fixed intervals
then force the radius to be five.

This closes the large-radius branch of Goldschmidt (6.11), printed p.402,
directly from (6.11.3), without a second track construction.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}
/-- Reversal of the exact commutator forces a large odd radius to be five. -/
theorem CanonicalLabelSetup.radius_eq_five_of_odd_track_commutator
    (d : CanonicalLabelSetup F s)
    (hcomm : ∀ e : CanonicalLabelSetup F s, e.radius=d.radius →
      ⁅e.label (e.track.vertex e.center),
          e.label (e.track.vertex (e.center+(e.radius:ℤ)+3))⁆ =
        e.label (e.track.vertex (e.center+4)))
    (hodd : Odd d.radius) : d.radius=5 := by
  obtain ⟨k,hk⟩ := hodd
  let n : ℤ := (k:ℤ)+2
  have hn : 2*n=(d.radius:ℤ)+3 := by dsimp [n]; omega
  let a := d.track.translation^n
  let p : ℤ → RankTwo.Vertex F := fun i => d.track.vertex (d.center+i)
  let z : ℤ → G := fun i => d.label (p i)
  have ht (i : ℤ) : (p (2*i)).type=d.side := d.shifted_type i
  have htrans (i : ℤ) : a • p i=p (i+2*n) := by
    simpa only [a,p,add_assoc] using d.track.zpow_translate n (d.center+i)
  have hlabel (i : ℤ) (hi : (p i).type=d.side) :
      (MulAut.conj a) (z i)=z (i+2*n) := by
    change a*d.label (p i)*a⁻¹=d.label (p (i+2*n))
    rw [← htrans,d.conjugate _ _ hi]
  have hleft : ⁅z 0,z (2*n)⁆=z 4 := by
    simpa only [z,p,add_zero,hn,add_assoc] using hcomm d rfl
  have hright : ⁅z 0,z (-2*n)⁆=z (-4) := by
    have hh := hcomm d.reverse rfl
    change ⁅d.label (d.track.vertex (-(-d.center))),
      d.label (d.track.vertex (-(-d.center+(d.radius:ℤ)+3)))⁆ =
        d.label (d.track.vertex (-(-d.center+4))) at hh
    simpa only [neg_neg,show -(-d.center+(d.radius:ℤ)+3)=d.center+(-2*n) by omega,
      show -(-d.center+4)=d.center+(-4) by omega,z,p,add_zero] using hh
  have hright' := congrArg (MulAut.conj a) hright
  rw [map_commutatorElement,hlabel 0 (ht 0),hlabel (-2*n)
    (by simpa only [show (2:ℤ)*(-n)= -2*n by ring] using ht (-n)),hlabel (-4)
    (by simpa only [show (2:ℤ)*(-2) = -4 by norm_num] using ht (-2))] at hright'
  simp only [zero_add,show -2*n+2*n=0 by ring] at hright'
  have hlabels : z 4=z (-4+2*n) := by
    calc
      z 4=(z 4)⁻¹ := (d.label_inv (ht 2)).symm
      _=⁅z 0,z (2*n)⁆⁻¹ := congrArg Inv.inv hleft.symm
      _=⁅z (2*n),z 0⁆ := commutatorElement_inv _ _
      _=z (-4+2*n) := hright'
  have he : (2:ℤ)=n-2 := d.shifted_label_injective
    (by simpa only [z,p,show (2:ℤ)*2=4 by norm_num,
      show (2:ℤ)*(n-2)= -4+2*n by omega] using hlabels)
  omega

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
