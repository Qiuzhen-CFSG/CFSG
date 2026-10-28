module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Core
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Models
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Obstruction

/-!
# The component-structure step of 15.3.33(3)

The earlier 1.1.5 implications remain explicit universal inputs. The local
Sylow and centralizer data construct their hypotheses using 15.3.33(2), with
M_c in the role of M. For ordinary components, noncontainment in the original
M follows separately from F*(M ∩ I) = O₂(M ∩ I). The odd-core conclusion
follows from subnormality and O(I) = 1.

For every source C-component, the odd core and characteristic-two centralizer
clauses are proved without treating it as ordinary. The remaining reduction
is exact: either all five desired clauses hold, or F*(K) = O₂(K). Excluding
this second branch from the local conclusions of 15.3.2--12 and 15.3.25 is
still required before asserting the full source 15.3.33(3). In particular,
O(I) = 1 alone is not used to identify the two component conventions.
`Obstruction` further shows that the remaining nonordinary C-components lie
inside M, using the proved extension argument of 15.3.33(1).

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.33, printed p.1134; Definition A.3.1, p.41; 1.1.5, pp.501--503.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- Universal source 1.1.5(1), using the equivalent self-centralizing-core
formulation of characteristic two. The intersection is intrinsic to H. -/
def Earlier115One (κ : GroupClass) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (_ : IsSimpleQTKE κ G) (H : Subgroup G) (P : Sylow 2 H) (M : Subgroup G) (z : G),
    Chapter1.Lemma115Hypotheses H P M z →
      HasCharacteristicTwo (M.subgroupOf H)

/-- Universal source 1.1.5(3), for ordinary components only, with every model
and action clause retained. It does not assert a result about C-components. -/
def Earlier115Three (κ : GroupClass) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (_ : IsSimpleQTKE κ G) (H : Subgroup G) (P : Sylow 2 H) (M : Subgroup G) (z : G),
    Chapter1.Lemma115Hypotheses H P M z →
      ∀ K : Subgroup H, IsComponent H K →
        K.map H.subtype = ⁅K.map H.subtype, zpowers z⁆ ∧
          ¬ K.map H.subtype ≤ M ∧ HasModelAction115 K z

/-- All five conclusions of 15.3.33(3). This is an output interface, with
literal relative subgroups, commutators, model actions and centralizers. -/
structure Conclusions {I : Subgroup G} (K : Subgroup I) (M : Subgroup G) (z : G) : Prop where
  outside : ¬ K.map I.subtype ≤ M
  commutator : K.map I.subtype = ⁅K.map I.subtype, zpowers z⁆
  model_action : HasModelAction115 K z
  odd_core : pPrimeCore 2 K = ⊥
  centralizer_core : generalizedFitting (centralizerIn K z) = pCore 2 (centralizerIn K z)

/-- The two core conclusions for every source C-component, independently
of the missing comparison with ordinary components. -/
theorem cComponent_cores {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlierOne : Earlier115One κ G)
    {Yplus S M Mc I : Subgroup G} (T : Sylow 2 G)
    (hI : I ∈ outsideFamily Yplus S M) (hSylow : OutsideSylowControl Yplus S M)
    (hST : S ≤ (T : Subgroup G)) (hMc : Mc ∈ Chapter1.HeOver G (T : Set G))
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ S)
    (hzcentral : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hCz : centralizer ({z} : Set G) = Mc) (hodd : pPrimeCore 2 I = ⊥)
    {K : Subgroup I} (hK : K.IsCComponent) :
    pPrimeCore 2 K = ⊥ ∧
      generalizedFitting (centralizerIn K z) = pCore 2 (centralizerIn K z) := by
  obtain ⟨P, _, hlocal⟩ := lemma_15_3_33_2 T hI hSylow hST hMc hz hzS hzcentral hCz
  refine ⟨cComponent_oddCore_eq_bot hK hodd,
    centralizerIn_characteristicTwo hK.subnormal z ?_⟩
  rw [hCz]
  exact earlierOne hG I P Mc z hlocal

/-- All clauses for an actual ordinary component. The two overgroups M
and M_c have separate roles throughout the proof. -/
theorem ordinary_component_structure {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlierOne : Earlier115One κ G) (earlierThree : Earlier115Three κ G)
    {Yplus S M Mc I : Subgroup G} (T : Sylow 2 G)
    (hI : I ∈ outsideFamily Yplus S M) (hSylow : OutsideSylowControl Yplus S M)
    (hST : S ≤ (T : Subgroup G)) (hMc : Mc ∈ Chapter1.HeOver G (T : Set G))
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ S)
    (hzcentral : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hCz : centralizer ({z} : Set G) = Mc) (hodd : pPrimeCore 2 I = ⊥)
    (hMI : generalizedFitting (M.subgroupOf I) = pCore 2 (M.subgroupOf I))
    {K : Subgroup I} (hK : IsComponent I K) : Conclusions K M z := by
  obtain ⟨P, _, hlocal⟩ := lemma_15_3_33_2 T hI hSylow hST hMc hz hzS hzcentral hCz
  obtain ⟨hcomm, _, hmodel⟩ := earlierThree hG I P Mc z hlocal K hK
  obtain ⟨ho, hc⟩ := cComponent_cores hG earlierOne T hI hSylow hST hMc hz hzS
    hzcentral hCz hodd (component_isCComponent hK)
  refine ⟨?_, hcomm, hmodel, ho, hc⟩
  intro hKM
  exact component_not_le_characteristicTwo hK hMI (map_le_iff_le_comap.mp hKM)

/-- Reduction of the source C-component statement. The characteristic-two
branch is an outstanding local obstruction, not a classification alternative
from 1.1.5 and not a discharged premise of 15.3.33(3). -/
theorem cComponent_structure_or_characteristicTwo {κ : GroupClass}
    (hG : IsSimpleQTKE κ G)
    (earlierOne : Earlier115One κ G) (earlierThree : Earlier115Three κ G)
    {Yplus S M Mc I : Subgroup G} (T : Sylow 2 G)
    (hI : I ∈ outsideFamily Yplus S M) (hSylow : OutsideSylowControl Yplus S M)
    (hST : S ≤ (T : Subgroup G)) (hMc : Mc ∈ Chapter1.HeOver G (T : Set G))
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ S)
    (hzcentral : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hCz : centralizer ({z} : Set G) = Mc) (hodd : pPrimeCore 2 I = ⊥)
    (hMI : generalizedFitting (M.subgroupOf I) = pCore 2 (M.subgroupOf I))
    {K : Subgroup I} (hK : K.IsCComponent) :
    Conclusions K M z ∨ generalizedFitting K = pCore 2 K := by
  rcases cComponent_ordinary_or_characteristicTwo hK hodd with hK | hK
  · exact Or.inl (ordinary_component_structure hG earlierOne earlierThree T hI hSylow
      hST hMc hz hzS hzcentral hCz hodd hMI hK)
  · exact Or.inr hK

end CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
