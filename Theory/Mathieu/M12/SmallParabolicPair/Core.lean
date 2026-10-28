module

public import Theory.Mathieu.M12.SmallParabolicPair.Seeds
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic

/-!
# The embedded plus-type quaternion core in M₁₂

The four marked permutations give two injective quaternion representations.
Their images commute and meet precisely in the distinguished involution.
Their join therefore has order 32 and is extraspecial of plus type, with the
actual factor embeddings retained. Identification with O₂ of the first
parabolic is a separate local-order calculation.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

noncomputable def quaternionMap (i j : M12) : QuaternionGroup 2 → M12
  | .a n => i ^ n.val
  | .xa n => j * i ^ n.val

noncomputable def leftEmbedding : QuaternionGroup 2 →* M12 where
  toFun := quaternionMap leftI leftJ
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

noncomputable def rightEmbedding : QuaternionGroup 2 →* M12 where
  toFun := quaternionMap rightI rightJ
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem leftEmbedding_injective : Function.Injective leftEmbedding := by decide +kernel
theorem rightEmbedding_injective : Function.Injective rightEmbedding := by decide +kernel

noncomputable def leftFactor : Subgroup M12 := leftEmbedding.range
noncomputable def rightFactor : Subgroup M12 := rightEmbedding.range
noncomputable def core : Subgroup M12 := leftFactor ⊔ rightFactor

theorem factors_commute : ∀ b ∈ leftFactor, ∀ c ∈ rightFactor, b * c = c * b := by
  have h : ∀ q r : QuaternionGroup 2,
      leftEmbedding q * rightEmbedding r = rightEmbedding r * leftEmbedding q := by
    decide +kernel
  rintro _ ⟨q,rfl⟩ _ ⟨r,rfl⟩
  exact h q r

theorem factors_intersection_mem (g : M12) :
    g ∈ leftFactor ⊓ rightFactor ↔ g = 1 ∨ g = z := by
  constructor
  · rintro ⟨⟨q,rfl⟩,⟨r,hr⟩⟩
    have h : ∀ q r : QuaternionGroup 2, rightEmbedding r = leftEmbedding q →
        leftEmbedding q = 1 ∨ leftEmbedding q = z := by decide +kernel
    exact h q r hr
  · rintro (rfl | rfl)
    · exact ⟨leftFactor.one_mem, rightFactor.one_mem⟩
    · exact ⟨⟨QuaternionGroup.a 2, by decide +kernel⟩,
        ⟨QuaternionGroup.a 2, by decide +kernel⟩⟩

theorem factors_intersection_card : Nat.card (leftFactor ⊓ rightFactor : Subgroup M12) = 2 := by
  have he : (↑(leftFactor ⊓ rightFactor) : Set M12) = {1,z} := by
    ext g
    exact (factors_intersection_mem g).trans (by simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff])
  rw [← SetLike.coe_sort_coe, he, Nat.card_coe_set_eq]
  apply Set.ncard_pair
  decide +kernel

noncomputable def coreQuaternionData : Subgroup.QuaternionCentralProductData core where
  left := leftFactor.subgroupOf core
  right := rightFactor.subgroupOf core
  left_model := ⟨(Subgroup.subgroupOfEquivOfLe (show leftFactor ≤ core from le_sup_left)).trans
    (MonoidHom.ofInjective leftEmbedding_injective).symm⟩
  right_model := ⟨(Subgroup.subgroupOfEquivOfLe (show rightFactor ≤ core from le_sup_right)).trans
    (MonoidHom.ofInjective rightEmbedding_injective).symm⟩
  intersection_card := by
    change Nat.card ((leftFactor ⊓ rightFactor).subgroupOf core) = 2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show leftFactor ⊓ rightFactor ≤ core from inf_le_left.trans le_sup_left)).toEquiv]
    exact factors_intersection_card
  commute := by
    intro b hb c hc
    exact Subtype.ext (factors_commute b.val hb c.val hc)
  span := by
    rw [← Subgroup.subgroupOf_sup (show leftFactor ≤ core from le_sup_left)
      (show rightFactor ≤ core from le_sup_right)]
    exact Subgroup.subgroupOf_self _

theorem card_core : Nat.card core = 32 := coreQuaternionData.card

theorem extraspecial_core : IsExtraspecial 2 core := coreQuaternionData.extraspecial

theorem mem_core (g : M12) :
    g ∈ core ↔ ∃ q r : QuaternionGroup 2, leftEmbedding q * rightEmbedding r = g := by
  have hn : leftFactor ≤ Subgroup.normalizer (rightFactor : Set M12) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro b hb c hc
    exact (factors_commute b hb c hc).symm
  change g ∈ (↑(leftFactor ⊔ rightFactor) : Set M12) ↔ _
  rw [Subgroup.coe_mul_of_left_le_normalizer_right leftFactor rightFactor hn]
  constructor
  · rintro ⟨b,⟨q,rfl⟩,c,⟨r,rfl⟩,h⟩
    exact ⟨q,r,h⟩
  · rintro ⟨q,r,rfl⟩
    exact ⟨_,⟨q,rfl⟩,_,⟨r,rfl⟩,rfl⟩

theorem z_mem_core : z ∈ core :=
  (show leftFactor ≤ core from le_sup_left) ((factors_intersection_mem z).mpr (Or.inr rfl)).1

theorem natural_le_core : natural ≤ core := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases hx with rfl | rfl
  · exact z_mem_core
  · apply (mem_core v).mpr
    decide +kernel

theorem elementary_le_core : elementary ≤ core := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact z_mem_core
  · exact natural_le_core v_mem_natural
  · apply (mem_core third).mpr
    decide +kernel

theorem core_le_firstParabolic : core ≤ firstParabolic := by
  intro g hg
  obtain ⟨q,r,rfl⟩ := (mem_core g).mp hg
  rw [firstParabolic, Subgroup.mem_centralizer_singleton_iff]
  have h : ∀ q r : QuaternionGroup 2,
      leftEmbedding q * rightEmbedding r * z = z * (leftEmbedding q * rightEmbedding r) := by
    decide +kernel
  exact h q r

end Sporadic.Mathieu.M12SmallPair
