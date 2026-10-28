module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure

/-!
# The outside-component route through 15.3.33

The component chosen immediately before 15.3.33 is an ordinary component L
of I. It lies outside M because M intersect I has characteristic two. The
existing ordinary-component theorem therefore supplies every clause of
`Conclusions` for this chosen L without excluding C-components inside M.

More generally, the local extension argument shows that a C-component of I
outside M is ordinary. We combine that result with the ordinary-component
theorem. The containing-component adapters retain actual subgroup images:
if L lies outside M and its image is contained in a C-component K of another
eligible outside overgroup, then K lies outside M and has the same five
conclusions. Existence of such a containing C-component remains the separate
embedding theorem's obligation.

Source-use audit: the uses of 15.3.33(3) in 15.3.34, 15.3.37, 15.3.39,
the setup of 15.3.41, and the completion of 15.3.35 concern the selected L.
The repeated reduction in 15.3.38 uses L contained in L1 in C(I1), with
I1 = N_G(V1) in the outside family; the adapters below give ordinary status
and the conclusions for L1. The corresponding uses in 15.3.43 again concern
the selected L and its centralizer quotient. The applications of 15.3.33(1)
to invariant Borels are unchanged.

This does not prove the universal assertion in printed 15.3.33(3). It also
does not supply Yplus not contained in the larger L1, or the separate
embedding and two-component arguments in C_G(v) and C_G(f). Those groups
are not asserted to belong to the outside family. Quotient conclusions are
transported from the selected ordinary component, rather than obtained by
reapplying this theorem to a quotient.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, printed
pp.1134--1140, especially the choice of L on p.1134 and the enlargement to
I1 on p.1136. No later containment or uniqueness result is used here.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure.Outside

variable {G : Type*} [Group G] [Finite G]

/-- The selected ordinary component has its source center identity and all
five conclusions, independently of the unresolved inside-C-component case. -/
theorem exists_ordinary_component_structure {κ : GroupClass}
    (hG : IsSimpleQTKE κ G)
    (earlierOne : Earlier115One κ G) (earlierThree : Earlier115Three κ G)
    {Yplus S M Mc I : Subgroup G} (T : Sylow 2 G)
    (hI : I ∈ outsideFamily Yplus S M) (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hST : S ≤ (T : Subgroup G)) (hMc : Mc ∈ Chapter1.HeOver G (T : Set G))
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ S)
    (hzcentral : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hCz : centralizer ({z} : Set G) = Mc) (hodd : pPrimeCore 2 I = ⊥)
    (hFMI : generalizedFitting (M.subgroupOf I) = pCore 2 (M.subgroupOf I)) :
    ∃ L : Subgroup I, IsComponent I L ∧ center L = pCore 2 L ∧ Conclusions L M z := by
  obtain ⟨L, hL, _, hcenter, _, _⟩ := exists_component_for_outside hI h25 hodd hFMI
  exact ⟨L, hL, hcenter, ordinary_component_structure hG earlierOne earlierThree T
    hI hSylow hST hMc hz hzS hzcentral hCz hodd hFMI hL⟩

/-- Every C-component outside M is ordinary and satisfies all five clauses
of the source conclusion. The local hypotheses are uniform over the outside
family because the nonordinary-component obstruction uses 15.3.33(1). -/
theorem cComponent_structure_of_outside {κ : GroupClass}
    (hG : IsSimpleQTKE κ G)
    (earlierOne : Earlier115One κ G) (earlierThree : Earlier115Three κ G)
    {Yplus S M Mc I : Subgroup G} (T : Sylow 2 G)
    (hI : I ∈ outsideFamily Yplus S M) (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hFMI : generalizedFitting (M.subgroupOf I) = pCore 2 (M.subgroupOf I))
    (hST : S ≤ (T : Subgroup G)) (hMc : Mc ∈ Chapter1.HeOver G (T : Set G))
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ S)
    (hzcentral : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hCz : centralizer ({z} : Set G) = Mc)
    {K : Subgroup I} (hK : K.IsCComponent) (hKM : ¬ K.map I.subtype ≤ M) :
    IsComponent I K ∧ Conclusions K M z := by
  have ho : IsComponent I K :=
    (cComponent_ordinary_iff_outside hI hSylow h25 hodd hSM hMI hY hFMI hK).mpr hKM
  exact ⟨ho, ordinary_component_structure hG earlierOne earlierThree T hI hSylow
    hST hMc hz hzS hzcentral hCz (hodd I hI) hFMI ho⟩

/-- A containing C-component inherits noncontainment from an actual ambient
subgroup. This applies even when the two overgroups are not nested; the new
overgroup must still satisfy all displayed outside-family hypotheses. -/
theorem cComponent_structure_of_containing {κ : GroupClass}
    (hG : IsSimpleQTKE κ G)
    (earlierOne : Earlier115One κ G) (earlierThree : Earlier115Three κ G)
    {Yplus S M Mc I : Subgroup G} (T : Sylow 2 G)
    (hI : I ∈ outsideFamily Yplus S M) (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hFMI : generalizedFitting (M.subgroupOf I) = pCore 2 (M.subgroupOf I))
    (hST : S ≤ (T : Subgroup G)) (hMc : Mc ∈ Chapter1.HeOver G (T : Set G))
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ S)
    (hzcentral : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hCz : centralizer ({z} : Set G) = Mc)
    {K : Subgroup I} (hK : K.IsCComponent)
    {L : Subgroup G} (hLM : ¬ L ≤ M) (hLK : L ≤ K.map I.subtype) :
    IsComponent I K ∧ Conclusions K M z :=
  cComponent_structure_of_outside hG earlierOne earlierThree T hI hSylow h25 hodd
    hSM hMI hY hFMI hST hMc hz hzS hzcentral hCz hK (fun hKM => hLM (hLK.trans hKM))

/-- The relative containing-lift adapter for the enlargement I0 ≤ I.
The embedding theorem supplies `K` and `hLK`; the seed component's already
proved conclusions supply its noncontainment in M. The output concerns the
literal subgroup K of the larger I, with no ambient normality assumption. -/
theorem cComponent_structure_of_containing_lift {κ : GroupClass}
    (hG : IsSimpleQTKE κ G)
    (earlierOne : Earlier115One κ G) (earlierThree : Earlier115Three κ G)
    {Yplus S M Mc I : Subgroup G} (T : Sylow 2 G)
    (hI : I ∈ outsideFamily Yplus S M) (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hFMI : generalizedFitting (M.subgroupOf I) = pCore 2 (M.subgroupOf I))
    (hST : S ≤ (T : Subgroup G)) (hMc : Mc ∈ Chapter1.HeOver G (T : Set G))
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ S)
    (hzcentral : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hCz : centralizer ({z} : Set G) = Mc)
    {I0 : Subgroup G} (hI0I : I0 ≤ I) {L : Subgroup I0}
    (hL : Conclusions L M z) {K : Subgroup I} (hK : K.IsCComponent)
    (hLK : L.map (inclusion hI0I) ≤ K) : IsComponent I K ∧ Conclusions K M z := by
  have hLK' : L.map I0.subtype ≤ K.map I.subtype := by
    calc
      L.map I0.subtype = (L.map (inclusion hI0I)).map I.subtype := by
        rw [map_map]
        rfl
      _ ≤ K.map I.subtype := map_mono hLK
  exact cComponent_structure_of_containing hG earlierOne earlierThree T hI hSylow
    h25 hodd hSM hMI hY hFMI hST hMc hz hzS hzcentral hCz hK hL.outside hLK'

end CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure.Outside
