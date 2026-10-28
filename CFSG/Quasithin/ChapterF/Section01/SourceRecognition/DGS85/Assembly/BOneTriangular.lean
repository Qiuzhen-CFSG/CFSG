module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreeSplitQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourceWeylParameter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneFullProfiles
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.LinearFlagTransport
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Data.Fintype.Shrink

/-!
# Recognition of the original triangular natural branch

The source r=3 elation theorem identifies the conjugated roots in the whole
Borel image of the actual apartment quotient. Its marked split quotient
therefore has Weyl rotation order three. The natural-profile recognition
selects PSL₃ over the source field, with the full Borel and both endpoint
inclusion squares. Shrinking the field preserves this marked comparison.

For the original nonsolvable b=1 critical pair, both full-Cartan profiles
are constructed internally. Only its source r=3 branch is selected here;
the central r=4 branch is retained by BOneTriangularConsumers.
Source: DGS, Groups and Graphs (1985), (10.5), pp.156--157, (3.7), p.80,
and Theorem D, p.224; Fong--Seitz I (6A)(a), II (7C),(8A).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
universe u uF
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)
variable (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4)

/-- The chosen quotient has the literal source rotation order three. -/
theorem triangular_quotient_rotation : rotationOrder (fullCartanRThreeFiniteQuotient ds hr)=3 := by
  have hlen := (fullCartanProfiles_parameters ds).1.unique hr.1
  have he : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S))
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots ds)))
      (fullCartanPathLength ds) := by
    rw [hlen]
    exact fullCartan_source_exchange_of_r_three ds hr
  have ho := finiteQuotient_simple_product_order h c (fullCartanPathRoots ds)
    (fullCartanRoots_normalizes ds) (fullCartanRoots_a ds) (fullCartanRoots_b ds)
    (fullCartanRoots_square ds) (fullCartanPathLength ds) (fullCartanPathLength_gt ds)
    (fullCartanProfiles_path_odd ds) (fullCartanProfiles_path_transitive ds) he
    (fullCartan_quotient_root_sign_of_r_three ds hr)
  exact ho.trans hlen

include hr in
/-- Recognize the reduced triangular amalgam over its original right field. -/
theorem triangular_reduced_comparison :
    ∃ point : Bool, Nonempty (Iso (reducedAmalgam L S)
      (LinearNative.amalgam (ds true).F point)) := by
  let p : C2Source.Profile L S (ds false).F (ds true).F (ds false).W (ds true).W :=
    ⟨(ds false).data,(ds true).data,(ds false).actor_eq,(ds true).actor_eq,(ds false).dimension⟩
  rcases reduced_comparison h p (ds true).dimension (fullCartanRThreeFiniteQuotient ds hr)
    (fullCartanRThreeFiniteMarkedIso ds hr) (fullCartanRThreeFiniteSplitData ds hr) with hh | hh
  · exact hh.2
  · have := triangular_quotient_rotation ds hr
    omega

include hr in
/-- A small field carrier for the same triangular comparison and source field size. -/
theorem small_triangular_reduced_comparison :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (m : ℕ), 0 < m ∧ Nat.card F = 2^m ∧ Nat.card F = Nat.card (ds true).F ∧
      ∃ point : Bool, Nonempty (Iso (reducedAmalgam L S) (LinearNative.amalgam F point)) := by
  obtain ⟨point,⟨f⟩⟩ := triangular_reduced_comparison ds hr
  let F := Shrink.{0} (ds true).F
  let a : (ds true).F ≃+* F := (Shrink.ringEquiv.{0,_} (ds true).F).symm
  let : CharP F 2 := (a.toRingHom.charP_iff_charP 2).mp inferInstance
  let := Fintype.ofFinite F
  obtain ⟨m,_,hF⟩ := FiniteField.card F 2
  have hf : Iso (LinearNative.amalgam (ds true).F point) (LinearNative.amalgam F point) := by
    cases point
    · exact Matrix.PSL3.RootPresentationRecognition.flagFieldIso a 0
    · exact Matrix.PSL3.RootPresentationRecognition.flagFieldIso a 1
  exact ⟨F,inferInstance,inferInstance,inferInstance,m,m.property,
    by simpa only [Nat.card_eq_fintype_card] using hF,
    Nat.card_congr a.symm.toEquiv,point,⟨f.trans hf⟩⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original triangular critical branch has an actual reduced linear-three
comparison, with no marked quotient, splitness or recognition hypothesis. -/
theorem small_linear_comparison_of_critical_bOne_rThree
    (h : HypothesisF11 L S)
    (hns : ∀ j : Fin 2, ¬ Group.IsSolvable (parabolic L S j))
    {v w : RankTwo.Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S)=1)
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (m : ℕ), 0 < m ∧ Nat.card F = 2^m ∧
      ∃ point : Bool, Nonempty (Iso (reducedAmalgam L S) (LinearNative.amalgam F point)) := by
  obtain ⟨ds⟩ := full_cartan_profiles_of_critical_bOne h hns hc hne hb (chosenCartans h)
  obtain ⟨F,_,_,_,m,hm,hF,_,point,hiso⟩ := small_triangular_reduced_comparison ds hr
  exact ⟨F,inferInstance,inferInstance,inferInstance,m,hm,hF,point,hiso⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
