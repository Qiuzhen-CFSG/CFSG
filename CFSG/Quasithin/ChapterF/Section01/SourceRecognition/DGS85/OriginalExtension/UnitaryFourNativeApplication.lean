module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UnitaryFourNative
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ResidualMarking
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourReduced

/-!
# Original U₄ markings from the literal reduced pair

Native restoration constructs the original full endpoint and overlap maps.
The equality of embedded original and reduced solvable residuals then
constructs the exact existing U₄ marking. This supplies the original-marking
premise in the selected-factor diagram exclusion and native involution
placement, for either orientation and every nonbinary degree.

The original outer action remains present. Neither the degree-two extension
nor the full Borel is discarded. Reduced recognition and the final restriction
of the permitted outer action remain separate source obligations.
Source: DGS (1985), (15.2), pp.226–228; Aschbacher–Smith F.1.12, pp.263–264,
5.2.6–7, pp.650–651, and F.4.35, p.292.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open Chapter6.Source.RankOneGeneric

/-- Both original residual and inner endpoint markings follow from the
same reduced comparison. Perfectness of the selected factors is not needed. -/
theorem exists_original_unitaryFour_marking_of_reduced_iso
    {G : Type*} [Group G] {L R S : Subgroup G}
    (h : HypothesisF11 ![L,R] S) (m : ℕ) (hm : 1 ≤ m) (hmgt : 1 < m)
    (point : Bool)
    (e : Iso (reducedAmalgam ![L,R] S) (UnitaryFourNative.amalgam m hm point)) :
    Nonempty (Global.OriginalUnitaryFour.Marking m hm point L R S) := by
  let U := UnitaryFourNative.extension h m hm point e hmgt
  obtain ⟨E,_,hl,hr⟩ := UnitaryFourNative.exists_original_extension_iso h m hm point e hmgt
  exact ⟨residualMarkingOfRestoredIso h U E e.left e.right hl hr⟩

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (hmgt : 1 < m) (point : Bool)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) (UnitaryFourNative.amalgam m hm point))

include d h hTH hp hmgt e
/-- The restored original U₄ maps rule out the literal noncentral diagram
layer, without assuming an original marking or a collapsed extension. -/
theorem not_reduced_unitaryFour_of_layer
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hl : Global.NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R)) : False := by
  obtain ⟨f⟩ := exists_original_unitaryFour_marking_of_reduced_iso
    (d.hypothesisF11 h hTH) m hm hmgt point e
  exact d.not_original_unitaryFour_of_layer h hTH hp hN hl m hm point f

/-- The same reduced marking fixes the actual original local Sylow
intersections and their orders, while retaining the possible outer part of S. -/
theorem unitaryFour_original_intersections_of_reduced_iso :
    Global.sourceS L H ⊓ R = (T : Subgroup G) ⊓ L ∧
      Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) = (2^m)^6 := by
  obtain ⟨f⟩ := exists_original_unitaryFour_marking_of_reduced_iso
    (d.hypothesisF11 h hTH) m hm hmgt point e
  have hs := d.original_unitaryFour_intersections h hTH hp m hm point f
  have hc := (d.original_unitaryFour_intersections_card h hTH hp m hm point f).1
  rw [d.left_intersection] at hc
  exact ⟨hs.symm.trans d.left_intersection,hc⟩

/-- Native involution placement now uses the original selected factor
cores and literal reduced endpoints of the consumer. -/
theorem unitaryFour_original_involution_placement_of_reduced_iso
    (x : G) (hx : x ∈ parabolic ![L,R] ((T : Subgroup G) ⊓ L) 0 ⊓
      parabolic ![L,R] ((T : Subgroup G) ⊓ L) 1) (hx2 : x^2=1) :
    (∃ g ∈ parabolic ![L,R] ((T : Subgroup G) ⊓ L) 0, g*x*g⁻¹ ∈ R.pCoreIn 2) ∨
    (∃ g ∈ parabolic ![L,R] ((T : Subgroup G) ⊓ L) 1, g*x*g⁻¹ ∈ L.pCoreIn 2) := by
  obtain ⟨f⟩ := exists_original_unitaryFour_marking_of_reduced_iso
    (d.hypothesisF11 h hTH) m hm hmgt point e
  exact d.original_unitaryFour_involution_placement h hTH hp m hm point f x hx hx2

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
