module

public import Theory.GroupTheory.GeneralizedFitting.PCoreImageCommutator
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary

/-!
# Component commutators and critical-edge generation

The intrinsic prime-core image theorem proves the component commutator
calculation in 13.8.18(1). Here it is applied inside the endpoint group J,
then transported back to the ambient group to feed the existing actual
conjugate-span generation lemma.

The source inputs are J = KE, relative normality and two-perfectness of K,
quasisimplicity of its actual image in J/O₂(J), U_H ≤ O₂(E), and
D_H = U_H ∩ O₂(J). The last two are earlier F.9/component inputs, to be
discharged by the parent source assembly. For every F ≤ U_H outside D_H,
the result is J = ⟨F^J⟩E, with the given edge stabilizer E unchanged.
It neither assumes [K,F] = K nor replaces D_H with an arbitrary label.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma
13.8.18(1), printed p.953 (PDF p.970), using F.9.13(2), printed p.322.
The endpoint conjugator and the other clauses of 13.8.18 belong to the
parent CriticalGeometry assembly.
-/

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The generation step of 13.8.18(1), for every actor outside the actual
F.9 denominator. The earlier F.9 and component inputs remain explicit;
normality is relative to J and K* is the actual image in J/O₂(J). -/
public theorem generation_of_edge_two_core
    (J K E U_H Uγ A₁ : Subgroup G) (hJ : J = K ⊔ E)
    (hK : (K.subgroupOf J).Normal)
    (hres : pResidual 2 (K.subgroupOf J) = ⊤)
    (hqs : IsQuasisimple (Source.starImage J K))
    (hU : U_H ≤ E.pCoreIn 2)
    (hD : Source.DH U_H Uγ A₁ = U_H ⊓ J.pCoreIn 2) :
    ∀ F : Subgroup G, F ≤ U_H → ¬ F ≤ Source.DH U_H Uγ A₁ →
      J = conjugateSpanBy F J ⊔ E := by
  intro F hFU hFD
  have hKJ : K ≤ J := by rw [hJ]; exact le_sup_left
  have hEJ : E ≤ J := by rw [hJ]; exact le_sup_right
  have hFE : F ≤ E.pCoreIn 2 := hFU.trans hU
  have hFJ : F ≤ J := hFE.trans ((pCoreIn_le 2 E).trans hEJ)
  let := hK
  let : IsQuasisimple ((K.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) := hqs
  have hgen : K.subgroupOf J ⊔ E.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup hKJ hEJ, ← hJ, subgroupOf_self]
  have hFE' : F.subgroupOf J ≤ (E.subgroupOf J).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hFJ,
      map_pCoreIn_of_ker_isPGroup J.subtype
        (IsPGroup.ker_isPGroup_of_injective J.subtype_injective),
      map_subgroupOf_eq_of_le hEJ]
    exact hFE
  have hF' : ¬ F.subgroupOf J ≤ pCore 2 J := by
    intro hc
    apply hFD
    rw [hD]
    refine le_inf hFU ?_
    have hm := map_mono (f := J.subtype) hc
    rwa [map_subgroupOf_eq_of_le hFJ] at hm
  have hc := commutator_eq_left_of_quasisimple_pCore_image 2
    (K.subgroupOf J) (E.subgroupOf J) (F.subgroupOf J) hgen hres hFE' hF'
  have hm := congrArg (Subgroup.map J.subtype) hc
  rw [map_commutator, map_subgroupOf_eq_of_le hKJ,
    map_subgroupOf_eq_of_le hFJ] at hm
  exact generation_of_commutator_component J K E F hJ hFJ hm.symm

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
