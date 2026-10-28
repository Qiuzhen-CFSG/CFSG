module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitaryFiniteComparison
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FullNonElementaryMarkedProfile

/-!
# The constructed finite U₅ comparison for every positive source degree

The constructed apartment quotient, split data and rotation order four
feed the full nonelementary profile. The original alpha parabolic index
identifies the recognized field degree with the supplied degree. This
removes the original nonsolvability premise from the earlier finite
comparison, including the beta groups PSU₃(2) and SU₃(2).

The original alpha catalogue, actual beta unitary marking and Chapter 14
Cartans, reflections, exchange and root signs remain explicit. Both
endpoint maps and the full original Borel map belong to the same quotient
and the same U₅ comparison. No ambient-completion identification is claimed.
Source: DGS (1985), (11.8), pp.175--177, (14.1)--(14.2), pp.210--211,
and Theorem D, p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan

variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}

variable (h : HypothesisF11 L₀ S₀)
    (hc : IsCriticalPair (Reduction.reducedFamily L₀ S₀)
      (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) false)
      (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) true))
    (hb : DGS85.b (Reduction.reducedFamily L₀ S₀) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L₀ S₀)
        (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) false),
        Z (Reduction.reducedFamily L₀ S₀)
        (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) true)⁆ = ⊥)
    (Ma : IsRankOneModel
      ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
        (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) false)).map
          (Reduction.G₀ L₀ S₀).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
          (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) false)).map
            (Reduction.G₀ L₀ S₀).subtype)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU
        ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
          (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) true)).map
            (Reduction.G₀ L₀ S₀).subtype ⧸
          pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
            (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) true)).map
              (Reduction.G₀ L₀ S₀).subtype)) 3 (2^m) ∨
      IsSU ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
        (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) true)).map
          (Reduction.G₀ L₀ S₀).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
          (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) true)).map
            (Reduction.G₀ L₀ S₀).subtype)) 3 (2^m))
    (cartans : CompatibleCartans L₀ (reducedSylow L₀ S₀))
    (t : Bool → (reducedAmalgam L₀ S₀).Universal)
    (htfix : ∀ i, t i • Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) i = Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) i)
    (htmove : ∀ i, t i • Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) (!i) ≠ Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) (!i))
    (htsq : ∀ i, t i * t i = 1)
    (htnorm : ∀ i, t i ∈ normalizer (cartan cartans : Set (reducedAmalgam L₀ S₀).Universal))

include h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm

variable
    (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L₀ S₀).Universal) (sourceGraph (reducedAmalgam L₀ S₀))
      (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
        (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm))) 4)
    (hsign : ∀ i x, x ∈ apartmentGroup cartans
        (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm) →
      (∀ r ∈ (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t
          htfix htmove htsq htnorm i).root, quotientMap (reducedAmalgam L₀ S₀)
        (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
          (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)))
          4 (x⁻¹*r*x) ∈
        (originalMiddle (reducedAmalgam L₀ S₀)).map (quotientMap (reducedAmalgam L₀ S₀)
          (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
            (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)))
            4)) ∨
      (∀ r ∈ (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t
          htfix htmove htsq htnorm i).root, quotientMap (reducedAmalgam L₀ S₀)
        (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
          (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)))
          4
          (((originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t
            htfix htmove htsq htnorm i).reflection*x)⁻¹*r*
            ((originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t
              htfix htmove htsq htnorm i).reflection*x)) ∈
        (originalMiddle (reducedAmalgam L₀ S₀)).map (quotientMap (reducedAmalgam L₀ S₀)
          (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
            (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)))
            4)))

include h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm hexchange hsign

/-- The full U₅ comparison uses the constructed quotient and its proved
rotation order. The nonelementary premise is discharged by the actual
PSU₃/SU₃ marking on the original graph quotient. The original alpha
index identifies the output field degree with the supplied degree m. -/
theorem originalUnitaryFiniteComparisonFromMarking :
    Nonempty (FongSeitzBinary.UnitarySource.Combined.FiveComparison
      (originalUnitaryFiniteQuotient h hc hb hcomm Ma hm mark cartans t
        htfix htmove htsq htnorm hexchange hsign)
      (originalUnitaryFiniteMarkedIso h hc hb hcomm Ma hm mark cartans t
        htfix htmove htsq htnorm hexchange hsign) m false) := by
  have hne : letI := FongSeitzBinary.QuadrangleStructure.original_core_normal_in_sylow (L := L₀) (S := reducedSylow L₀ S₀) 1
      ¬ IsElementaryAbelian 2 (reducedSylow L₀ S₀ ⧸
        ((parabolic L₀ (reducedSylow L₀ S₀) 1).pCoreIn 2).subgroupOf (reducedSylow L₀ S₀)) := by
    have he := original_borel_unitary_quotient_not_elementary h hm mark
    have hq : (Q (Reduction.reducedFamily L₀ S₀)
        (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) true)).map (Reduction.G₀ L₀ S₀).subtype =
        (parabolic L₀ (reducedSylow L₀ S₀) 1).pCoreIn 2 :=
      (NoncommutingProfile.reduced_base_Q_map h true).trans (reduced_parabolic_core h 1).symm
    rw [hq] at he
    obtain ⟨hN,hne⟩ := he
    exact hne
  let quot := originalUnitaryFiniteQuotient h hc hb hcomm Ma hm mark cartans t
    htfix htmove htsq htnorm hexchange hsign
  let e := originalUnitaryFiniteMarkedIso h hc hb hcomm Ma hm mark cartans t
    htfix htmove htsq htnorm hexchange hsign
  let split := originalUnitaryFiniteSplitData h hc hb hcomm Ma hm mark cartans t
    htfix htmove htsq htnorm hexchange hsign
  have hrot := originalUnitaryFiniteRotationOrder h hc hb hcomm Ma hm mark cartans t
    htfix htmove htsq htnorm hexchange hsign
  obtain ⟨n,hn,k,hFk,hfink,hchk,E,hFE,hfinE,hchE,⟨profile⟩⟩ :=
    original_borel_nonElementary_marked_profile h hc hb hcomm Ma
      (mark.elim (.projective_unitary m hm) (.special_unitary m hm)) hne quot e split hrot
  have hidx : (commonBorel L₀ (reducedSylow L₀ S₀)).relIndex
      (parabolic L₀ (reducedSylow L₀ S₀) 0) = 2^(2*m)+1 := by
    let F := Reduction.reducedFamily L₀ S₀
    let G₀ := Reduction.G₀ L₀ S₀
    have hv := (original_unitary_field_and_valences h hc hb hcomm Ma hm mark).2
      (Subgroup.CosetGeometry.base F false)
    change Nat.card ((Subgroup.CosetGeometry.RankTwo.graph F).neighborSet
      (Subgroup.CosetGeometry.base F false)) = 2^(2*m)+1 at hv
    rw [Subgroup.CosetGeometry.RankTwo.card_neighbor_base] at hv
    change ((Reduction.P₀ L₀ S₀ 1).subgroupOf G₀).relIndex
      ((Reduction.P₀ L₀ S₀ 0).subgroupOf G₀) = 2^(2*m)+1 at hv
    have ht := (Reduction.reduced_triple h).intersection
    rw [←inf_relIndex_right,inf_comm,ht] at hv
    rw [←Reduction.B₀_eq_source h,←Reduction.P₀_eq_source h]
    exact (relIndex_subgroupOf (show Reduction.P₀ L₀ S₀ 0 ≤ G₀ from le_sup_left)).symm.trans hv
  have hp : 2^(2*n) = 2^(2*m) := by
    have hi := profile.linear_index
    rw [hidx] at hi
    simpa only [←pow_mul,Nat.mul_comm n 2] using (Nat.add_right_cancel hi).symm
  have hnm : n = m := by
    have hh := Nat.pow_right_injective (by decide : 1 < (2:ℕ)) hp
    omega
  subst n
  exact FongSeitzBinary.UnitaryFiveSource.five_source_theorem quot e split
    h hrot k E m hm false profile

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
