module

public import Stellmacher.SectionTwo.LemmaTwoFive
public import Stellmacher.UniqueMaximalContainingMap
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Odd automorphism orbits at Sylow index three

In a solvable characteristic-two group with Sylow index three and no
nontrivial characteristic Sylow subgroup normal in the ambient group,
the centralizer of the canonical omega-center module is exactly the
two-core. The faithful three-coset quotient is therefore SL2(2).
Stellmacher (2.5) now produces a nontrivial normal ambient subgroup whose
Sylow preimage is invariant under any prescribed odd automorphism group.

This discharges the local pushing-up input in Aschbacher--Smith F.6.13,
printed p.307, using the proved odd-orbit theorem in Stellmacher (2.5).
-/

public section
open Subgroup Stellmacher
open scoped Pointwise
namespace Stellmacher.SectionTwo
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem unique_of_index_three (S : Sylow 2 G) (hi : (S : Subgroup G).index = 3) :
    IsUniqueMaximalContaining (S : Subgroup G) ⊤ := by
  have hco := isCoatom_of_index_three (S : Subgroup G) hi
  apply (uniqueMaximalContaining_top_iff _).mpr
  refine ⟨S, hco, le_rfl, ?_⟩
  intro M hM hSM
  exact ((hco.le_iff).mp hSM).resolve_left hM.ne_top

private theorem cSubgroup_eq_core_of_index_three
    (h : Hypotheses G) (S : Sylow 2 G) (hi : (S : Subgroup G).index = 3)
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup G).subtype).Normal) :
    cSubgroup S = pCore 2 G := by
  obtain ⟨hc, hnot, _⟩ := two_four_initial_reduction h S hP (unique_of_index_three S hi)
  have hSC : (S : Subgroup G) ≤ centralizer (zSubgroup S : Set G) := by
    intro s hs
    rw [mem_centralizer_iff]
    rintro z ⟨zS, ⟨zC, hz, rfl⟩, rfl⟩
    exact congrArg (fun x : S => (x : G)) (mem_center_iff.mp zC.property ⟨s, hs⟩).symm
  have hCC : cSubgroup S ≤ centralizer (zSubgroup S : Set G) :=
    centralizer_le (show zSubgroup S ≤ vSubgroup S from le_normalClosure)
  have hCS : cSubgroup S ≤ (S : Subgroup G) := by
    by_contra hout
    have htop : (S : Subgroup G) ⊔ cSubgroup S = ⊤ := by
      rcases (isCoatom_of_index_three (S : Subgroup G) hi).le_iff.mp
        (le_sup_left : (S : Subgroup G) ≤ (S : Subgroup G) ⊔ cSubgroup S) with ht | he
      · exact ht
      · exact (hout (le_sup_right.trans he.le)).elim
    have hz : zSubgroup S ≤ center G := centralizer_eq_top_iff_subset.mp
      (top_unique (htop ▸ sup_le hSC hCC))
    have hv : vSubgroup S ≤ center G := normalClosure_le_normal hz
    exact hnot (hv.trans (center_le_centralizer _))
  change centralizer (vSubgroup S : Set G) ≤ (S : Subgroup G) at hCS
  change centralizer (vSubgroup S : Set G) = pCore 2 G
  rw [hc, inf_eq_right.mpr hCS]

/-- An odd automorphism group of the Sylow subgroup preserves a nontrivial
subgroup whose actual ambient image is normal. -/
theorem odd_invariant_normal_subgroup_of_index_three
    (h : Hypotheses G) (S : Sylow 2 G) (hi : (S : Subgroup G).index = 3)
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup G).subtype).Normal)
    (U : Subgroup (MulAut S)) (hU : Odd (Nat.card U)) :
    ∃ N : Subgroup S, N ≠ ⊥ ∧ (N.map (S : Subgroup G).subtype).Normal ∧
      ∀ a ∈ U, N.map (a : S →* S) ≤ N := by
  classical
  have hu := unique_of_index_three S hi
  have hC := cSubgroup_eq_core_of_index_three h S hi hP
  obtain ⟨hcore, hnot, _⟩ := two_four_initial_reduction h S hP hu
  have hproper : pCore 2 G < (S : Subgroup G) := by
    apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal S)
    intro he
    have hSC : (S : Subgroup G) ≤ centralizer (vSubgroup S : Set G) :=
      he ▸ hcore.le.trans inf_le_right
    exact hnot (le_centralizer_iff.mp ((sSup_le fun _ ha => ha.1).trans hSC))
  obtain ⟨j⟩ := sylow_index_three_core_quotient S hi hproper
  let q := QuotientGroup.mk' (pCore 2 G)
  have hk : q.ker = cSubgroup S := (QuotientGroup.ker_mk' _).trans hC.symm
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  obtain ⟨K, hK, hn, _⟩ := lemma_two_five h S hP hu q (QuotientGroup.mk'_surjective _)
    hk ⟨j.trans e.symm⟩ U hU
  let V := vSubgroupInSylow S
  let N : Subgroup S := ⨆ a : U, V.map (a.val : S →* S)
  have hmap : N.map (S : Subgroup G).subtype = K := by
    rw [hK, show N = ⨆ a : U, V.map (a.val : S →* S) from rfl, Subgroup.map_iSup]
    rfl
  have hVmap : V.map (S : Subgroup G).subtype = vSubgroup S := by
    apply Subgroup.map_comap_eq_self
    simpa using (vSubgroup_le_twoCore_and_elementaryAbelian h S).1.trans
      (pCore_isPGroup.le_sylow_of_normal S)
  have hVN : V ≤ N := by
    have hh := le_iSup (fun a : U => V.map (a.val : S →* S)) (1 : U)
    have hone : ((1 : MulAut S) : S →* S) = MonoidHom.id S := rfl
    simpa only [OneMemClass.coe_one, hone, Subgroup.map_id] using hh
  refine ⟨N, ?_, by rw [hmap]; exact hn, ?_⟩
  · intro hb
    have hvb : vSubgroup S = ⊥ := by
      rw [← hVmap, le_bot_iff.mp (hVN.trans hb.le), Subgroup.map_bot]
    exact hnot (hvb ▸ bot_le)
  · intro a ha
    have hmono (a : MulAut S) (ha : a ∈ U) : N.map (a : S →* S) ≤ N := by
      rw [show N = ⨆ a : U, V.map (a.val : S →* S) from rfl, Subgroup.map_iSup]
      apply iSup_le
      intro b
      have hm : (V.map (b.val : S →* S)).map (a : S →* S) =
          V.map (((⟨a,ha⟩ : U) * b).val : S →* S) := by
        rw [map_map]
        rfl
      rw [hm]
      exact le_iSup (fun a : U => V.map (a.val : S →* S)) _
    exact hmono a ha

end Stellmacher.SectionTwo
