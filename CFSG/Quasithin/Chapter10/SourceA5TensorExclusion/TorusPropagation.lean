module
public import CFSG.Quasithin.Chapter4.Section01.Maximality
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CommutatorPreimage.Membership
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Cartan propagation for the final tensor exclusions

A normalizer of the old component also normalizes the centralizer of its
2-core quotient. Hence a Cartan factor centralizing that quotient propagates
to its full normalizer orbit. If that orbit contains a cubic inside the old
A₅ component, centerlessness of A₅ and the two-core give a contradiction.

This is the common final step of Aschbacher–Smith 9.3.8 and 9.3.9. The actual
model identification of the centralizing Cartan factor, and the original
Cartan-orbit equality, are retained as earlier source inputs.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter4
variable {G : Type*} [Group G]

theorem source_tensor_torus_section_propagation (K D E N : Subgroup G)
    (hNK : N ≤ normalizer (K : Set G))
    (hEC : E ≤ sectionCentralizer K)
    (hgen : componentOrbit E N = D) : D ≤ sectionCentralizer K := by
  have hn : N ≤ normalizer (sectionCentralizer K : Set G) := by
    apply commutatorPreimage_normalized
    · exact normalizer_le_normalizer_characteristic_image K (pCore 2 K)
    · exact hNK.trans (normalizer (K : Set G)).le_normalizer
    · exact hNK
    · exact hNK.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  exact hgen ▸ iSup_conjugates_le_of_le_normalizer E N _ hEC hn

theorem source_tensor_torus_cubic_contradiction (K D E N : Subgroup G)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hNK : N ≤ normalizer (K : Set G))
    (hEC : E ≤ sectionCentralizer K)
    (hgen : componentOrbit E N = D)
    (b : G) (hbD : b ∈ D) (hbK : b ∈ K) (hb3 : orderOf b = 3) : False := by
  let q := QuotientGroup.mk' (pCore 2 K)
  have hDC := source_tensor_torus_section_propagation K D E N hNK hEC hgen
  have hcomm := (le_sectionCentralizer_iff D K).mp hDC |>.2
  have hbZ : eK (q ⟨b,hbK⟩) ∈ center (alternatingGroup (Fin 5)) := by
    rw [mem_center_iff]
    intro a
    obtain ⟨k,hk⟩ := (eK.surjective.comp (QuotientGroup.mk'_surjective _)) a
    rw [←hk]
    change eK (q k) * eK (q ⟨b,hbK⟩) = eK (q ⟨b,hbK⟩) * eK (q k)
    apply Eq.symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement,←map_commutatorElement]
    apply (map_eq_one_iff eK eK.injective).mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    have hm := hcomm (commutator_mem_commutator hbD k.property)
    exact (mem_map_iff_mem K.subtype_injective).mp hm
  rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hbZ
  have hbQ : b ∈ K.pCoreIn 2 := by
    exact mem_map_of_mem K.subtype ((QuotientGroup.eq_one_iff _).mp
      ((map_eq_one_iff eK eK.injective).mp hbZ))
  have hp : IsPGroup 3 (zpowers b) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hb3]; rfl)
  have hd := hp.disjoint_of_coprime (isPGroup_pCoreIn 2 K) (by decide)
  have hb1 : b = 1 := mem_bot.mp ((hd.eq_bot) ▸ (show b ∈ zpowers b ⊓ K.pCoreIn 2 from
    ⟨mem_zpowers b,hbQ⟩))
  simp [hb1] at hb3

end CFSG.Quasithin.Chapter10
