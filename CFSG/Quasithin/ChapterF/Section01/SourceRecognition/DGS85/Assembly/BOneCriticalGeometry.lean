module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneFullProfiles
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreeCompletion

/-!
# Original critical pairs give the marked r=3 geometric completion

Construct the paired full-Cartan profiles from the original nonsolvable
b=1 critical branch. Their actual path alternatives give r=3 or r=4.
For r=3, the earlier center calculation, natural exchange and canonical
root fusion now have all their profile inputs supplied. Separation yields
trivial endpoint kernels and preservation of the full overlap. The same
quotient homomorphism gives a faithful completion and a marked amalgam
isomorphism with both endpoint squares and the whole middle map recorded.

This construction is before the BN-pair argument. It does not identify the
full stabilizers of vertex classes with the original endpoint images, and
therefore does not discharge the Borel-image root-sign premise. The r=4
alternative is retained with its genuine path parameters. BOneCriticalGeometryConsumers
applies the construction to the original Chapter 12 selected pair.

Source: DGS, Groups and Graphs (1985), (3.6), pp.77--78,
(10.5), pp.156--157, and (14.12)--(14.13), pp.217--218.
-/

open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open Subgroup.CosetGeometry.RankTwo hiding base

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
universe u uF
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}

/-- A finite geometric quotient of the literal universal amalgam, with its
kernel, whole overlap, both endpoint squares and original middle map. This
asserts no Tits system or identification of full class stabilizers. -/
def HasMarkedGeometricQuotient
    (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j) : Prop :=
  let A := reducedAmalgam L S
  let n := fullCartanPathLength ds
  let T := cartanApartment A (apartmentGroup c (fullCartanPathRoots ds))
  Finite (QuotientGroup A T n) ∧
  (∀ i : Bool, kernel A T n ⊓ Universal.cosetFamily A i = ⊥) ∧
  (leftMap A T n).range ⊓ (rightMap A T n).range =
    (CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.middleMap A T n).range ∧
  (∃ d : FaithfulCompletion A (G := QuotientGroup A T n),
    d.left = leftMap A T n ∧ d.right = rightMap A T n) ∧
  ∃ e : Iso A (ofSubgroups (leftMap A T n).range
      ((leftMap A T n).range ⊓ (rightMap A T n).range) (rightMap A T n).range
      inf_le_left inf_le_right),
    (∀ x, (e.left x : QuotientGroup A T n) = quotientMap A T n (Universal.left A x)) ∧
    (∀ x, (e.right x : QuotientGroup A T n) = quotientMap A T n (Universal.right A x)) ∧
    (∀ x, (e.middle x : QuotientGroup A T n) =
      quotientMap A T n (Universal.left A (A.left x)))

/-- In the r=3 branch of the original critical pair, all full-Cartan
profile and coordinate inputs to exchange, canonical long-root fusion and
the literal faithful finite completion are discharged. The r=4 source
alternative is retained with its actual path parameters. -/
theorem marked_geometry_of_critical_bOne
    (h : HypothesisF11 L S)
    (hns : ∀ j : Fin 2, ¬ Group.IsSolvable (parabolic L S j))
    {v w : RankTwo.Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v, Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1)
    (c : CompatibleCartans L (reducedSylow L S)) :
    ∃ ds : ∀ j : Bool, FullCartanReflectionProfile.{u} h c j,
      (HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4 ∧
        HasMarkedGeometricQuotient ds ∧
        ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
          (sourceGraph (reducedAmalgam L S))
          (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots ds))) 3 ∧
        ∀ j : Bool, ∃ x ∈ (fullCartanPathRoots ds j).root, orderOf x = 2 ∧
          ∃ g ∈ universalBOneActor h j (ds j).data,
            g*x*g⁻¹ = fullCartanReflections ds j) ∨
      HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5 := by
  obtain ⟨ds⟩ := full_cartan_profiles_of_critical_bOne h hns hc hne hb c
  refine ⟨ds,?_⟩
  rcases fullCartanPathLength_cases ds with hn | hn
  · have hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4 := by
      simpa only [hn] using fullCartanProfiles_parameters ds
    refine Or.inl ⟨hr,?_,fullCartan_source_exchange_of_r_three ds hr,?_⟩
    · exact ⟨fullCartan_quotient_finite ds,
        fullCartan_kernel_inf_endpoints_of_r_three ds hr,
        fullCartan_quotient_overlap_of_r_three ds hr,
        ⟨fullCartanRThreeCompletion ds hr,rfl,rfl⟩,
        fullCartanRThreeCompletionIso ds hr,
        fullCartanRThreeCompletionIso_left_apply ds hr,
        fullCartanRThreeCompletionIso_right_apply ds hr,
        fullCartanRThreeCompletionIso_middle_apply ds hr⟩
    · intro j
      exact fullCartanRoots_source_conjugacy_of_center_eq_bot ds j
        (fullCartan_centers_eq_bot_of_source_r_three ds hr j)
  · exact Or.inr (by simpa only [hn] using fullCartanProfiles_parameters ds)

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
