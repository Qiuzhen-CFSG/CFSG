module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelFacts

/-!
# Reversing the canonical labeling and distinguishing translated labels

Track reversal transports the exact fixed interval and maximal central
interval while retaining the canonical labeling. Distinct centers along
the track have distinct labels, since their exact fixed intervals differ.
These facts support the symmetric commutator and terminal radius arguments.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the symmetric
argument and final contradiction in (6.11), printed pp.401--403.
-/

@[expose] public section
open Subgroup SimpleGraph
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}
namespace CanonicalLabelSetup

def reverseInterval (d : CanonicalLabelSetup F s) :
    d.track.reverse.CentralInterval (d.label (d.track.reverse.vertex (-d.center))) where
  fixedLeft := -d.center-(d.radius+1)
  fixedRight := -d.center+(d.radius+1)
  centralLeft := -d.center-1
  centralRight := -d.center+1
  fixed_iff i := by
    change d.label (d.track.vertex (-(-d.center))) • d.track.vertex (-i)=d.track.vertex (-i) ↔ _
    rw [neg_neg,d.interval.fixed_iff,d.fixed_left,d.fixed_right]
    omega
  central_lt := by omega
  central i hil hir := by
    change d.track.reverse.CentralEdge (d.label (d.track.vertex (-(-d.center)))) i
    rw [neg_neg,Track.centralEdge_reverse_iff]
    apply d.interval.central
    · rw [d.central_left]
      omega
    · rw [d.central_right]
      omega
  maximal a b hab hc := by
    have hc' : ∀ i, a ≤ i → i<b → d.track.reverse.CentralEdge
        (d.label (d.track.vertex d.center)) i := by
      simpa only [Track.reverse,neg_neg] using hc
    have hh := d.interval.reverse.maximal a b hab hc'
    change b-a ≤  -d.interval.centralLeft-(-d.interval.centralRight) at hh
    rw [d.central_left,d.central_right] at hh
    omega

/-- The same canonical labeling, viewed on the oppositely oriented track. -/
def reverse (d : CanonicalLabelSetup F s) : CanonicalLabelSetup F s :=
  {d with
    track := d.track.reverse
    center := -d.center
    center_type := by simpa only [Track.reverse,neg_neg] using d.center_type
    interval := reverseInterval d
    central_left := rfl
    central_right := rfl
    fixed_left := rfl
    fixed_right := rfl}

/-- Distinct translated centers have distinct canonical labels, because the
left endpoints of their exact fixed intervals are distinct. -/
theorem shifted_label_injective (d : CanonicalLabelSetup F s) :
    Function.Injective (fun k:ℤ => d.label (d.track.vertex (d.center+2*k))) := by
  intro k l he
  change d.label (d.track.vertex (d.center+2*k))=d.label (d.track.vertex (d.center+2*l)) at he
  have hk : d.label (d.track.vertex (d.center+2*k)) •
      d.track.vertex (d.center+2*k-(d.radius+1)) =
        d.track.vertex (d.center+2*k-(d.radius+1)) :=
    (d.shifted_fixed_iff k _).2 ⟨le_rfl,by omega⟩
  have hl : d.label (d.track.vertex (d.center+2*l)) •
      d.track.vertex (d.center+2*l-(d.radius+1)) =
        d.track.vertex (d.center+2*l-(d.radius+1)) :=
    (d.shifted_fixed_iff l _).2 ⟨le_rfl,by omega⟩
  rw [he] at hk
  rw [← he] at hl
  have hk' := (d.shifted_fixed_iff l _).1 hk
  have hl' := (d.shifted_fixed_iff k _).1 hl
  omega

end CanonicalLabelSetup
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
