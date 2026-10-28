module

public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.PCoreCentralQuotient

/-!
# Characteristic p after quotienting inside the core

Suppose G has characteristic p and Z is normal inside Oₚ(G). If the
preimage of F*(G/Oₚ(G)) centralizes Z, then G/Z has characteristic p.
Indeed F*(G/Z) lies in the image of C_G(Z). The latter is a central
quotient of a normal subgroup of G, so it has characteristic p. Restricting
the Fitting subgroup and every component to this overgroup finishes the
argument.

Source application: Aschbacher--Smith, 14.6.9(j), printed p.1027.
The source preimage centrality is supplied by original 14.6.1(5).
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Restriction to an overgroup preserves every generator of F*(G). -/
theorem generalizedFitting_le_map_of_le
    (N : Subgroup G) (hF : generalizedFitting G ≤ N) :
    generalizedFitting G ≤ (generalizedFitting N).map N.subtype := by
  rw [generalizedFitting]
  apply sup_le
  · have hf : fittingSubgroup G ≤ N := (fitting_le_generalizedFitting G).trans hF
    let e := subgroupOfEquivOfLe hf
    let : Group.IsNilpotent ((fittingSubgroup G).subgroupOf N) :=
      Group.nilpotent_of_mulEquiv e.symm
    have hh : (fittingSubgroup G).subgroupOf N ≤ generalizedFitting N :=
      (show (fittingSubgroup G).subgroupOf N ≤ fittingSubgroup N from
        le_sSup ⟨inferInstance,inferInstance⟩).trans (fitting_le_generalizedFitting N)
    simpa only [map_subgroupOf_eq_of_le hf] using map_mono (f := N.subtype) hh
  · apply sSup_le
    intro K hK
    have hKN := (component_le_generalizedFitting G K hK).trans hF
    have hh := component_le_generalizedFitting N (K.subgroupOf N) (hK.subgroupOf hKN)
    simpa only [map_subgroupOf_eq_of_le hKN] using map_mono (f := N.subtype) hh

/-- The source centralization of the generalized-Fitting preimage makes the
literal quotient by Z a group of characteristic p. -/
theorem generalizedFitting_quotient_eq_pCore_of_preimage_centralizes
    (p : ℕ) [Fact p.Prime]
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G)
    (Z : Subgroup G) [Z.Normal] (hZQ : Z ≤ pCore p G)
    (hpre : (generalizedFitting (G ⧸ pCore p G)).comap
      (QuotientGroup.mk' (pCore p G)) ≤ centralizer (Z : Set G)) :
    generalizedFitting (G ⧸ Z) = pCore p (G ⧸ Z) := by
  let C := centralizer (Z : Set G)
  let q := QuotientGroup.mk' Z
  let Cq := C.map q
  let f := q.subgroupMap C
  have hC : centralizer (pCore p C : Set C) ≤ pCore p C :=
    normal_core_selfCentralizing hc C
  have hk : f.ker ≤ center C := by
    intro x hx
    have hz : (x : G) ∈ Z := (QuotientGroup.eq_one_iff (x : G)).mp
      (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
    exact mem_center_iff.mpr fun c => Subtype.ext ((c.property _ hz).symm)
  have hCq : generalizedFitting Cq = pCore p Cq :=
    generalizedFitting_eq_pCore_of_selfCentralizing p
      (f.centralizer_pCore_le_of_surjective_centralKernel (q.subgroupMap_surjective C) hk hC)
  let r : (G ⧸ Z) →* (G ⧸ pCore p G) :=
    QuotientGroup.map Z (pCore p G) (MonoidHom.id G) hZQ
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore p G) x
    exact ⟨q g,rfl⟩
  have hF : generalizedFitting (G ⧸ Z) ≤ Cq := by
    intro x hx
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective Z x
    have hh := map_generalizedFitting_le_of_surjective r hr
      (mem_map_of_mem r hx)
    exact mem_map_of_mem q (hpre hh)
  apply le_antisymm
  · have hh := generalizedFitting_le_map_of_le Cq hF
    rw [hCq] at hh
    exact hh.trans (le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,
      pCore_isPGroup.map Cq.subtype⟩)
  · exact (pCore_le_fitting _ p).trans (fitting_le_generalizedFitting _)
end Theory.GroupTheory
