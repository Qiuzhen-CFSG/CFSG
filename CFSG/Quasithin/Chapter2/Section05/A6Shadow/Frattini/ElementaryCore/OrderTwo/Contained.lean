module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.OrderTwo.Geometry

/-!
# The contained order-two branch of 2.5.24

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.568.
For B = (S ∩ K)S_C, the inner involution cover shows that every elementary
subgroup is contained in S_C E₁ or S_C E₂. Both have order eight and S
interchanges them. The source containment and tˣ = t z_K put the relevant
crossing image in B. Its relative centralizer is the actual local core,
so the family argument gives the required orbit for the original x.
No invariance of B under x is assumed or needed.
-/

public section

open Subgroup AlternatingSix.ShadowLocal
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable (d : EarlierSetup κ G)

/-- The smaller overgroup has exactly these two largest elementary subgroups. -/
theorem contained_family (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 2) :
    largestElementary ((d.S ⊓ d.K) ⊔ d.SC) =
      {d.SC ⊔ fourZero d, d.SC ⊔ fourOne d} := by
  let := hEA
  have hcover (F : Subgroup G) (hF : F ≤ (d.S ⊓ d.K) ⊔ d.SC)
      (hel : IsElementaryAbelian 2 F) : F ≤ d.SC ⊔ fourZero d ∨ F ≤ d.SC ⊔ fourOne d := by
    let := hel
    apply SubgroupClass.subset_union.mp
    intro a ha
    have hc : d.SC ≤ centralizer ((d.S ⊓ d.K : Subgroup G) : Set G) :=
      (d.centralizer_K ▸ inf_le_right).trans (centralizer_le inf_le_right)
    have hm : a ∈ ((d.S ⊓ d.K : Subgroup G) : Set G) * (d.SC : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left (d.S ⊓ d.K) d.SC
        (hc.trans (centralizer_le_normalizer _))]
      exact hF ha
    obtain ⟨k, hk, c, hcC, rfl⟩ := hm
    have hcomm : Commute k c := hc hcC k hk
    have hpow := elemPow_eq_one_of_isElementaryAbelian (p := 2) (k * c) ha
    rw [hcomm.mul_pow, elemPow_eq_one_of_isElementaryAbelian c hcC, mul_one] at hpow
    rcases inner_involution_cover d k hk hpow with hk0 | hk1
    · exact Or.inl ((d.SC ⊔ fourZero d).mul_mem
        ((show fourZero d ≤ d.SC ⊔ fourZero d from le_sup_right) hk0)
        ((show d.SC ≤ d.SC ⊔ fourZero d from le_sup_left) hcC))
    · exact Or.inr ((d.SC ⊔ fourOne d).mul_mem
        ((show fourOne d ≤ d.SC ⊔ fourOne d from le_sup_right) hk1)
        ((show d.SC ≤ d.SC ⊔ fourOne d from le_sup_left) hcC))
  have h0 := four_join_card d hcard (fourZero d) ((fourZero_le d).trans inf_le_right)
  have h1 := four_join_card d hcard (fourOne d) ((fourOne_le d).trans inf_le_right)
  have hb (F : Subgroup G) (hF : F ≤ (d.S ⊓ d.K) ⊔ d.SC)
      (hel : IsElementaryAbelian 2 F) : Nat.card F ≤ 8 := by
    rcases hcover F hF hel with h | h
    · exact (card_le_of_le h).trans_eq h0
    · exact (card_le_of_le h).trans_eq h1
  have h0mem : d.SC ⊔ fourZero d ∈ largestElementary ((d.S ⊓ d.K) ⊔ d.SC) :=
    ⟨sup_le le_sup_right ((fourZero_le d).trans le_sup_left),
      four_join_elementary d hEA _ ((fourZero_le d).trans inf_le_right),
      fun F hF hel => h0.symm ▸ hb F hF hel⟩
  have h1mem : d.SC ⊔ fourOne d ∈ largestElementary ((d.S ⊓ d.K) ⊔ d.SC) :=
    ⟨sup_le le_sup_right ((fourOne_le d).trans le_sup_left),
      four_join_elementary d hEA _ ((fourOne_le d).trans inf_le_right),
      fun F hF hel => h1.symm ▸ hb F hF hel⟩
  ext F
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hF
    rcases hcover F hF.1 hF.2.1 with h | h
    · exact Or.inl (eq_of_le_of_card_ge h (hF.2.2 _ h0mem.1 h0mem.2.1))
    · exact Or.inr (eq_of_le_of_card_ge h (hF.2.2 _ h1mem.1 h1mem.2.1))
  · rintro (rfl | rfl)
    · exact h0mem
    · exact h1mem

/-- Intersecting K S_C with S gives the actual smaller overgroup. -/
theorem inner_join_core_eq_intersection :
    (d.S ⊓ d.K) ⊔ d.SC = d.S ⊓ (d.K ⊔ d.SC) := by
  apply le_antisymm
  · exact sup_le (inf_le_inf_left _ le_sup_left) (le_inf d.sc_le_s le_sup_right)
  · rintro a ⟨haS, ha⟩
    have hc : d.SC ≤ centralizer (d.K : Set G) := d.centralizer_K ▸ inf_le_right
    have hm : a ∈ (d.K : Set G) * (d.SC : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (hc.trans (centralizer_le_normalizer _))]
      exact ha
    obtain ⟨k, hk, c, hcC, rfl⟩ := hm
    have hkS : k ∈ d.S := (d.S.mul_mem_cancel_right (d.sc_le_s hcC)).mp haS
    exact mul_mem_sup ⟨hkS, hk⟩ hcC

/-- Source containment, intersected with S, puts the relevant image in B. -/
theorem contained_image (hcard : Nat.card d.SC = 2) (hz : d.z = d.zK)
    (himage : rightConjugate d.x (fourZero d) ≤ d.K ⊔ d.SC) :
    rightConjugate d.x (d.SC ⊔ fourZero d) ≤ (d.S ⊓ d.K) ⊔ d.SC := by
  have hE : rightConjugate d.x (fourZero d) ≤ (d.S ⊓ d.K) ⊔ d.SC := by
    rw [inner_join_core_eq_intersection]
    exact le_inf (d.rightConjugate_le ((fourZero_le d).trans inf_le_left)) himage
  have hC : rightConjugate d.x d.SC ≤ (d.S ⊓ d.K) ⊔ d.SC := by
    nth_rw 1 [core_eq_zpowers_of_card_two d hcard]
    rw [rightConjugate, MonoidHom.map_zpowers]
    apply zpowers_le.mpr
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [d.crossing_t, hz]
    exact ((d.S ⊓ d.K) ⊔ d.SC).mul_mem
      ((show d.SC ≤ (d.S ⊓ d.K) ⊔ d.SC from le_sup_right) d.t_mem)
      ((show d.S ⊓ d.K ≤ (d.S ⊓ d.K) ⊔ d.SC from le_sup_left)
        (fourZero_le d (zK_mem_fourZero d)))
  exact (Subgroup.map_sup _ _ _).le.trans (sup_le hC hE)

/-- At order two adjoining the central core does not change the relative centralizer. -/
theorem relativeCentralizer_four_join (hcard : Nat.card d.SC = 2)
    (E : Subgroup G) :
    d.S ⊓ centralizer ((d.SC ⊔ E : Subgroup G) : Set G) =
      d.S ⊓ centralizer (E : Set G) := by
  apply le_antisymm (inf_le_inf_left _ (centralizer_le (show E ≤ d.SC ⊔ E from le_sup_right)))
  rintro a ⟨haS, haE⟩
  refine ⟨haS, ?_⟩
  have hC : d.SC ≤ centralizer ({a} : Set G) := by
    intro c hc
    exact mem_centralizer_singleton_iff.mpr (((core_le_center d hcard hc).2 a haS).symm)
  have hE : E ≤ centralizer ({a} : Set G) := by
    intro e he
    exact mem_centralizer_singleton_iff.mpr (haE e he)
  intro b hb
  exact mem_centralizer_singleton_iff.mp (sup_le hC hE hb)

/-- The contained order-two branch, for the original crossing element x.
This includes both fixation and exchange of the two elementary eight-groups. -/
theorem hasNormalizerOrbit_of_contained (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 2) (hz : d.z = d.zK)
    (hcore : ∀ E : Subgroup G, E ≤ d.S ⊓ d.K → IsKleinFour E →
      localCore d E = d.S ⊓ centralizer (E : Set G))
    (himage : rightConjugate d.x (fourZero d) ≤ d.K ⊔ d.SC) :
    HasNormalizerOrbit d := by
  apply hasNormalizerOrbit_of_centralizer_family d (fourZero d) (fourZero_le d)
    (d.SC ⊔ fourZero d) ((d.S ⊓ d.K) ⊔ d.SC) (d.SC ⊔ fourOne d)
  · rw [relativeCentralizer_four_join d hcard]
    exact hcore _ (fourZero_le d) inferInstance
  · exact contained_family d hEA hcard
  · exact contained_image d hcard hz himage
  · exact four_join_conjugate d

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo
