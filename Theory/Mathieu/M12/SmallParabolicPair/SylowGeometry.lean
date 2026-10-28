module
public import Theory.Mathieu.M12.SmallParabolicPair.Centralizers
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry.Counts
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry.FiniteGeometry
public import Theory.Mathieu.M12.Properties.Order
public import Theory.GroupTheory.PGroup.Omega
public import Mathlib.GroupTheory.Sylow

/-!
# Common Sylow subgroup of the marked M₁₂ parabolics

Enumeration of the natural-four normalizer gives orders 192 and 64 for the
second parabolic and the intersection. The ambient order makes this intersection
Sylow in M₁₂ and hence in each parabolic. Two hexads certify normality of the
elementary eight and its self-centralization in the intersection. Restriction
to the quaternion core then identifies the center and its first omega subgroup.

Source: Aschbacher–Smith, Hypothesis 14.2.1 and Lemma 14.2.21.
-/
@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
open SylowEnumeration
open scoped IsMulCommutative

theorem card_secondParabolic : Nat.card secondParabolic = 192 :=
  SylowEnumeration.secondParabolic_card

theorem card_sylowCandidate : Nat.card sylowCandidate = 64 :=
  SylowEnumeration.intersection_card

noncomputable def commonSylow : Sylow 2 M12 :=
  Sylow.ofCard sylowCandidate (by rw [card_sylowCandidate, m12_order]; decide +kernel)

@[simp] theorem commonSylow_coe : (commonSylow : Subgroup M12) = sylowCandidate := rfl

noncomputable def firstParabolicSylow : Sylow 2 firstParabolic :=
  commonSylow.subtype (show sylowCandidate ≤ firstParabolic from inf_le_left)

noncomputable def secondParabolicSylow : Sylow 2 secondParabolic :=
  commonSylow.subtype (show sylowCandidate ≤ secondParabolic from inf_le_right)

@[simp] theorem firstParabolicSylow_coe : (firstParabolicSylow : Subgroup firstParabolic) =
    sylowCandidate.subgroupOf firstParabolic := rfl

@[simp] theorem secondParabolicSylow_coe : (secondParabolicSylow : Subgroup secondParabolic) =
    sylowCandidate.subgroupOf secondParabolic := rfl

private theorem word_of_second (g : M12) (hg : g ∈ secondParabolic) :
    ∃ i : Fin 192, wordElement i = g := by
  have h := (mem_wordCarrier_iff g.val).mpr
    ⟨(mem_M12_iff_preservesBlocks _).mp g.property, (mem_secondParabolic_iff g).mp hg⟩
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
  exact ⟨i,Subtype.ext hi⟩

instance elementary_normal_secondParabolic :
    (elementary.subgroupOf secondParabolic).Normal where
  conj_mem := by
    intro e he g
    change g.val * e.val * g.val⁻¹ ∈ elementary
    change e.val ∈ elementary at he
    obtain ⟨a,ha⟩ := word_of_second g.val g.property
    rw [elementary_eq_range] at he ⊢
    obtain ⟨b,hb⟩ := he
    obtain ⟨c,hc⟩ := word_normalizes_elementary a b
    refine ⟨c,?_⟩
    simpa only [ha, hb] using hc.symm

theorem sylowCandidate_centralizer_elementary :
    sylowCandidate ⊓ Subgroup.centralizer (elementary : Set M12) = elementary := by
  apply le_antisymm
  · rintro g ⟨hg,hc⟩
    obtain ⟨a,ha⟩ := word_of_second g hg.2
    have hz := hc z (natural_le_elementary z_mem_natural)
    have hv := hc v (natural_le_elementary v_mem_natural)
    have ht := hc third (Subgroup.subset_closure (by simp))
    obtain ⟨c,hc⟩ := word_centralizer_elementary a
      (by simpa only [ha] using hz.symm)
      (by simpa only [ha] using hv.symm)
      (by simpa only [ha] using ht.symm)
    rw [elementary_eq_range]
    exact ⟨c,hc.trans ha⟩
  · intro g hg
    refine ⟨elementary_le_sylowCandidate hg, ?_⟩
    intro x hx
    exact congrArg Subtype.val (mul_comm (⟨x,hx⟩ : elementary) ⟨g,hg⟩)

theorem sylowCandidate_center_mem (g : sylowCandidate) :
    g ∈ Subgroup.center sylowCandidate ↔ (g : M12) = 1 ∨ (g : M12) = z := by
  constructor
  · intro hg
    have he : g.val ∈ elementary := by
      rw [← sylowCandidate_centralizer_elementary]
      refine ⟨g.property,?_⟩
      intro x hx
      exact congrArg (fun t : sylowCandidate => (t : M12)) (Subgroup.mem_center_iff.mp hg
        ⟨x,elementary_le_sylowCandidate hx⟩)
    have hc : (⟨g.val,elementary_le_core he⟩ : core) ∈ Subgroup.center core := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact congrArg (fun t : sylowCandidate => (t : M12)) (Subgroup.mem_center_iff.mp hg
        ⟨x.val,core_le_sylowCandidate x.property⟩)
    exact (core_center_mem _).mp hc
  · intro hg
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    rcases hg with h | h
    · change x.val * g.val = g.val * x.val
      simp [h]
    · change x.val * g.val = g.val * x.val
      rw [h]
      exact (Subgroup.mem_centralizer_singleton_iff.mp x.property.1)

theorem omega_center_image :
    ((omega₁ (Subgroup.center sylowCandidate) (p := 2)).map
      (Subgroup.center sylowCandidate).subtype).map sylowCandidate.subtype = distinguished := by
  apply le_antisymm
  · rintro g ⟨x,⟨y,_,hy⟩,hx⟩
    have h := (sylowCandidate_center_mem y.val).mp y.property
    have heq : (y.val : M12) = g := (congrArg Subtype.val hy).trans hx
    rw [heq] at h
    rcases h with rfl | rfl
    · exact distinguished.one_mem
    · exact Subgroup.mem_zpowers z
  · apply Subgroup.zpowers_le.mpr
    have hzT : z ∈ sylowCandidate := core_le_sylowCandidate z_mem_core
    have hzC : (⟨z,hzT⟩ : sylowCandidate) ∈ Subgroup.center sylowCandidate :=
      (sylowCandidate_center_mem _).mpr (Or.inr rfl)
    refine Subgroup.mem_map.mpr ⟨⟨z,hzT⟩,?_,rfl⟩
    refine Subgroup.mem_map.mpr ⟨⟨⟨z,hzT⟩,hzC⟩,?_,rfl⟩
    apply Subgroup.subset_closure
    change (⟨⟨z,hzT⟩,hzC⟩ : Subgroup.center sylowCandidate) ^ (2^1) = 1
    apply Subtype.ext
    apply Subtype.ext
    exact (by simpa [z_order] using pow_orderOf_eq_one z)
end Sporadic.Mathieu.M12SmallPair
