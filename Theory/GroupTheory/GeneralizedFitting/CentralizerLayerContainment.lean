module
public import Theory.GroupTheory.CComponent.FixedOrbitSelection
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import FeitThompson.FinalTheorem

/-!
# Components of a Sylow-centralizing subgroup centralizer

A component of C_G(A) lying in E(G) lies in an A-orbit of ordinary
components. If A centralizes a full Sylow two-subgroup, it normalizes each
ordinary component, because its simple central quotient has even order.
The orbit is therefore a single component.
Source: the ordinary containment step in Aschbacher--Smith 12.4.8, p.815,
using GLS II, B.5.22 and standard component calculus.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Full-Sylow centralization removes the component-orbit ambiguity in the
ordinary layer containment theorem. -/
theorem IsComponentIn.le_component_of_le_layer_of_centralizes_sylow
    {D A : Subgroup G} (hD : IsComponentIn D (centralizer (A : Set G)))
    (hlayer : D ≤ componentLayer G) (S : Sylow 2 G)
    (hA : A ≤ centralizer (S : Set G)) :
    ∃ J : Subgroup G, IsComponent G J ∧ D ≤ J := by
  obtain ⟨J,hJ,hDJ⟩ := IsCComponent.le_componentOrbit_of_le_componentLayer
    A hD.1 hD.2.isCComponent hlayer
  let := hJ.2
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  have heven : 2 ∣ Nat.card (J ⧸ center J) := by
    by_contra hn
    exact Group.IsPerfect.not_isSolvable (J ⧸ center J)
      (odd_order_theorem _ (Nat.not_even_iff_odd.mp (by
        simpa only [even_iff_two_dvd] using hn)))
  have hn := hJ.centralizes_sylow_normalizes S heven hA
  exact ⟨J,hJ,hDJ.trans (iSup_conjugates_le_of_le_normalizer J A J le_rfl hn)⟩

omit [Finite G] in
/-- Restrict a centralizer component to an overgroup containing the actor
and the component. The literal inclusion pulls back its subnormal chain. -/
theorem IsComponentIn.subgroupOf_centralizer
    {D A H : Subgroup G} (hD : IsComponentIn D (centralizer (A : Set G)))
    (hDH : D ≤ H) (hAH : A ≤ H) :
    IsComponentIn (D.subgroupOf H) (centralizer (A.subgroupOf H : Set H)) := by
  let C := centralizer (A.subgroupOf H : Set H)
  have hDC : D.subgroupOf H ≤ C := by
    intro d hd a ha
    exact Subtype.ext (hD.1 hd a ha)
  let f : C →* centralizer (A : Set G) :=
    (H.subtype.comp C.subtype).codRestrict _ (fun x a ha =>
      congrArg Subtype.val (x.property ⟨a,hAH ha⟩ ha))
  refine ⟨hDC,hD.2.1.comap f,?_⟩
  let := hD.quasisimple
  exact IsQuasisimple.of_mulEquiv
    ((subgroupOfEquivOfLe hDC).trans (subgroupOfEquivOfLe hDH)).symm

/-- A component whose simple central quotient is nonabelian is normalized
by every subgroup centralizing a full Sylow two-subgroup. -/
theorem IsComponent.normalized_of_centralizes_sylow
    {J A : Subgroup G} (hJ : IsComponent G J)
    (S : Sylow 2 G) (hA : A ≤ centralizer (S : Set G)) :
    A ≤ Subgroup.normalizer (J : Set G) := by
  let := hJ.2
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  have heven : 2 ∣ Nat.card (J ⧸ center J) := by
    by_contra hn
    exact Group.IsPerfect.not_isSolvable (J ⧸ center J)
      (odd_order_theorem _ (Nat.not_even_iff_odd.mp (by
        simpa only [even_iff_two_dvd] using hn)))
  exact hJ.centralizes_sylow_normalizes S heven hA

/-- The layer placement in a larger centralizer supplies an actual component
there, normalized by the original Sylow-centralizing actor. -/
theorem IsComponentIn.exists_containing_component_of_centralizes_sylow
    {D A H : Subgroup G} (hD : IsComponentIn D (centralizer (A : Set G)))
    (hAH : A ≤ H) (hlayer : D ≤ (componentLayer H).map H.subtype)
    (S : Sylow 2 H) (hA : A ≤ centralizer ((S : Subgroup H).map H.subtype : Set G)) :
    ∃ J : Subgroup G, IsComponentIn J H ∧ D ≤ J ∧ A ≤ Subgroup.normalizer (J : Set G) := by
  have hDH : D ≤ H := hlayer.trans (map_subtype_le _)
  have hlocal := hD.subgroupOf_centralizer hDH hAH
  have hlocalLayer : D.subgroupOf H ≤ componentLayer H := by
    intro d hd
    obtain ⟨e,he,hed⟩ := hlayer hd
    exact (Subtype.ext hed : e = d) ▸ he
  have hlocalA : A.subgroupOf H ≤ centralizer (S : Set H) := by
    intro a ha s hs
    exact Subtype.ext (hA ha s (mem_map_of_mem _ hs))
  obtain ⟨J,hJ,hDJ⟩ := hlocal.le_component_of_le_layer_of_centralizes_sylow
    hlocalLayer S hlocalA
  have hnJ := hJ.normalized_of_centralizes_sylow S hlocalA
  refine ⟨J.map H.subtype,⟨map_subtype_le _,?_⟩,?_,?_⟩
  · rwa [show (J.map H.subtype).subgroupOf H = J from
      comap_map_eq_self_of_injective H.subtype_injective J]
  · have hh := map_mono (f := H.subtype) hDJ
    rwa [map_subgroupOf_eq_of_le hDH] at hh
  · intro a ha
    exact J.le_normalizer_map H.subtype
      (mem_map_of_mem H.subtype (hnJ (show (⟨a,hAH ha⟩ : H) ∈ A.subgroupOf H from ha)))
end Theory.GroupTheory
