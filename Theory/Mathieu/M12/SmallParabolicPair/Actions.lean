module

public import Theory.Mathieu.M12.SmallParabolicPair.Geometry
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Defs

/-!
# Compatible local cubic actions in the concrete M₁₂ pair

The first-parabolic cubic acts nontrivially on each embedded quaternion factor.
We package its actual conjugation automorphisms for residual recognition. The
second-parabolic cubic normalizes the marked elementary eight and moves its
marked involution. These witnesses transport under an isomorphism of the
second parabolic, without extending it to an ambient-group isomorphism.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem movingActor_normalizes_elementary :
    movingActor ∈ Subgroup.normalizer (elementary : Set M12) := by
  apply Subgroup.mem_normalizer_fintype
  intro w hw
  rw [elementary_eq_range] at hw ⊢
  obtain ⟨a,rfl⟩ := hw
  have h : ∀ a : ElementaryCoordinates, ∃ b : ElementaryCoordinates,
      elementaryEmbedding b = movingActor * elementaryEmbedding a * movingActor⁻¹ := by
    decide +kernel
  exact h a

theorem cubicActor_normalizes_left :
    cubicActor ∈ Subgroup.normalizer (leftFactor : Set M12) := by
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨q,rfl⟩
  have h : ∀ q : QuaternionGroup 2, ∃ r : QuaternionGroup 2,
      leftEmbedding r = cubicActor * leftEmbedding q * cubicActor⁻¹ := by decide +kernel
  exact h q

theorem cubicActor_normalizes_right :
    cubicActor ∈ Subgroup.normalizer (rightFactor : Set M12) := by
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨q,rfl⟩
  have h : ∀ q : QuaternionGroup 2, ∃ r : QuaternionGroup 2,
      rightEmbedding r = cubicActor * rightEmbedding q * cubicActor⁻¹ := by decide +kernel
  exact h q

theorem leftFactor_core_image : coreQuaternionData.left.map core.subtype = leftFactor :=
  Subgroup.map_subgroupOf_eq_of_le (show leftFactor ≤ core from le_sup_left)

theorem rightFactor_core_image : coreQuaternionData.right.map core.subtype = rightFactor :=
  Subgroup.map_subgroupOf_eq_of_le (show rightFactor ≤ core from le_sup_right)

noncomputable def localCubic :
    Subgroup.QuaternionLocalCubic core firstParabolic coreQuaternionData where
  element := ⟨cubicActor,cubicActor_mem⟩
  order := cubicActor_order
  actionLeft := (coreQuaternionData.left.map core.subtype).normalizerMonoidHom
    ⟨cubicActor, by rw [leftFactor_core_image]; exact cubicActor_normalizes_left⟩
  actionRight := (coreQuaternionData.right.map core.subtype).normalizerMonoidHom
    ⟨cubicActor, by rw [rightFactor_core_image]; exact cubicActor_normalizes_right⟩
  actionLeft_apply _ := rfl
  actionRight_apply _ := rfl
  actionLeft_ne_one := by
    intro heq
    have hb : leftI ∈ coreQuaternionData.left.map core.subtype := by
      rw [leftFactor_core_image]
      exact ⟨QuaternionGroup.a 1, by decide +kernel⟩
    have h := congrArg (fun f : MulAut (coreQuaternionData.left.map core.subtype) =>
      (f ⟨leftI,hb⟩ : M12)) heq
    change cubicActor * leftI * cubicActor⁻¹ = leftI at h
    exact (by decide +kernel : cubicActor * leftI * cubicActor⁻¹ ≠ leftI) h
  actionRight_ne_one := by
    intro heq
    have hb : rightI ∈ coreQuaternionData.right.map core.subtype := by
      rw [rightFactor_core_image]
      exact ⟨QuaternionGroup.a 1, by decide +kernel⟩
    have h := congrArg (fun f : MulAut (coreQuaternionData.right.map core.subtype) =>
      (f ⟨rightI,hb⟩ : M12)) heq
    change cubicActor * rightI * cubicActor⁻¹ = rightI at h
    exact (by decide +kernel : cubicActor * rightI * cubicActor⁻¹ ≠ rightI) h

theorem moving_point_transport {A : Type*} [Group A] (e : secondParabolic ≃* A) :
    let E := (elementary.subgroupOf secondParabolic).map e.toMonoidHom
    let zA := e ⟨z,elementary_le_secondParabolic (natural_le_elementary z_mem_natural)⟩
    zA ∈ E ∧ ∃ y : A, y ∈ pResidual 2 A ∧
      y ∈ Subgroup.normalizer (E : Set A) ∧ y * zA * y⁻¹ ≠ zA := by
  let z₀ : secondParabolic :=
    ⟨z,elementary_le_secondParabolic (natural_le_elementary z_mem_natural)⟩
  let y₀ : secondParabolic := ⟨movingActor,movingActor_mem⟩
  have hz₀ : z₀ ∈ elementary.subgroupOf secondParabolic := natural_le_elementary z_mem_natural
  have hn : y₀ ∈ Subgroup.normalizer
      (elementary.subgroupOf secondParabolic : Set secondParabolic) := by
    exact Subgroup.le_normalizer_comap secondParabolic.subtype movingActor_normalizes_elementary
  have hm : y₀ * z₀ * y₀⁻¹ ≠ z₀ := by
    intro h
    have hval := congrArg (fun x : secondParabolic => (x : M12)) h
    change movingActor * z * movingActor⁻¹ = z at hval
    exact movingActor_moves hval
  obtain ⟨hz,hy,hnorm,hmove⟩ := Subgroup.map_residual_moving_point e
    (elementary.subgroupOf secondParabolic) z₀ hz₀ y₀ movingActor_residual hn hm
  exact ⟨hz,e y₀,hy,hnorm,hmove⟩

end Sporadic.Mathieu.M12SmallPair
