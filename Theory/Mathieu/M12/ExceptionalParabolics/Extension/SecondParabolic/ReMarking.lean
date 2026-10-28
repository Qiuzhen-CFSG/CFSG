module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.Movement
public import Theory.Mathieu.M12.SmallParabolicPair.Core

/-!
# Literal comparison with the original lifted quaternion factors

Two explicitly bijective quaternion homomorphisms describe the required
basis changes. Equality on the two quaternion generators proves equality
of the complete homomorphisms. The resulting subgroup equations retain
both original lifted factors and their central product, so downstream
residual embeddings can be aligned without identifying maps by their orders.
Source: Aschbacher--Smith, 14.2.21, printed p.988.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
open QuaternionSwapModel
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def leftChange : QuaternionGroup 2 →* QuaternionGroup 2 where
  toFun q := match q with
    | .a n => (QuaternionGroup.a 1) ^ n.val
    | .xa n => QuaternionGroup.xa 2 * (QuaternionGroup.a 1) ^ n.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def rightChange : QuaternionGroup 2 →* QuaternionGroup 2 where
  toFun q := match q with
    | .a n => (QuaternionGroup.xa 3) ^ n.val
    | .xa n => QuaternionGroup.xa 0 * (QuaternionGroup.xa 3) ^ n.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem leftChange_bijective : Function.Bijective leftChange := by decide +kernel
theorem rightChange_bijective : Function.Bijective rightChange := by decide +kernel

private theorem quaternionValue_a_one (i j : Carrier) : quaternionValue i j (.a 1) = i := by
  norm_num [quaternionValue, ZMod.val_one_eq_one_mod]

private theorem quaternionValue_xa_zero (i j : Carrier) : quaternionValue i j (.xa 0) = j := by
  simp [quaternionValue]

private theorem quaternion_hom_ext {G : Type*} [Group G] (f g : QuaternionGroup 2 →* G)
    (hi : f (.a 1) = g (.a 1)) (hj : f (.xa 0) = g (.xa 0)) : f = g := by
  apply MonoidHom.ext
  intro q
  have ha (n : ZMod 4) : QuaternionGroup.a n = (QuaternionGroup.a 1 : QuaternionGroup 2)^n.val := by
    rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
  have hx (n : ZMod 4) : QuaternionGroup.xa n =
      (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a n := by simp
  cases q with
  | a n => rw [ha, map_pow, map_pow, hi]
  | xa n => rw [hx, ha, map_mul, map_mul, map_pow, map_pow, hi, hj]

variable (m : InnerModel)

theorem embedding_left (q : QuaternionGroup 2) :
    m.embedding (M12SmallPair.leftEmbedding q) = quaternionValue leftI leftJ q := by
  cases q <;> simp only [M12SmallPair.leftEmbedding, MonoidHom.coe_mk, OneHom.coe_mk,
    M12SmallPair.quaternionMap, quaternionValue, map_mul, map_pow,
    map_leftI _ m.embedding_originalA m.embedding_originalB,
    map_leftJ _ m.embedding_originalA m.embedding_originalB]

theorem embedding_right (q : QuaternionGroup 2) :
    m.embedding (M12SmallPair.rightEmbedding q) = quaternionValue rightI rightJ q := by
  cases q <;> simp only [M12SmallPair.rightEmbedding, MonoidHom.coe_mk, OneHom.coe_mk,
    M12SmallPair.quaternionMap, quaternionValue, map_mul, map_pow,
    map_rightI _ m.embedding_originalA m.embedding_originalB,
    map_rightJ _ m.embedding_originalA m.embedding_originalB]

theorem movement_left_original (q : QuaternionGroup 2) :
    movement (leftEmbedding q) = m.embedding (M12SmallPair.leftEmbedding (leftChange q)) := by
  have he : leftMap = (m.embedding.comp M12SmallPair.leftEmbedding).comp leftChange := by
    apply quaternion_hom_ext
    · change leftMap (.a 1) = m.embedding (M12SmallPair.leftEmbedding (leftChange (.a 1)))
      rw [show leftChange (.a 1) = .a 1 from by decide +kernel, embedding_left]
      simp only [leftMap, MonoidHom.coe_mk, OneHom.coe_mk, quaternionValue_a_one]
      exact Subtype.ext leftIPerm_eq
    · change leftMap (.xa 0) = m.embedding (M12SmallPair.leftEmbedding (leftChange (.xa 0)))
      rw [show leftChange (.xa 0) = (QuaternionGroup.xa 0)⁻¹ from by decide +kernel,
        map_inv, map_inv, embedding_left]
      simp only [leftMap, MonoidHom.coe_mk, OneHom.coe_mk, quaternionValue_xa_zero]
      exact Subtype.ext leftJPerm_eq
  rw [movement_left]
  exact congrArg (fun f : QuaternionGroup 2 →* Carrier => f q) he

theorem movement_right_original (q : QuaternionGroup 2) :
    movement (rightEmbedding q) = m.embedding (M12SmallPair.rightEmbedding (rightChange q)) := by
  have he : rightMap = (m.embedding.comp M12SmallPair.rightEmbedding).comp rightChange := by
    apply quaternion_hom_ext
    · change rightMap (.a 1) = m.embedding (M12SmallPair.rightEmbedding (rightChange (.a 1)))
      rw [show rightChange (.a 1) = ((QuaternionGroup.xa 0) * QuaternionGroup.a 1)⁻¹ from by decide +kernel]
      simp only [map_inv, map_mul, embedding_right]
      simp only [rightMap, MonoidHom.coe_mk, OneHom.coe_mk,
        quaternionValue_xa_zero, quaternionValue_a_one]
      exact Subtype.ext rightIPerm_eq
    · change rightMap (.xa 0) = m.embedding (M12SmallPair.rightEmbedding (rightChange (.xa 0)))
      rw [show rightChange (.xa 0) = .xa 0 from by decide +kernel, embedding_right]
      simp only [rightMap, MonoidHom.coe_mk, OneHom.coe_mk, quaternionValue_xa_zero]
      exact Subtype.ext rightJPerm_eq
  rw [movement_right]
  exact congrArg (fun f : QuaternionGroup 2 →* Carrier => f q) he

theorem movement_leftFactor : leftFactor.map movement = M12SmallPair.leftFactor.map m.embedding := by
  ext x
  constructor
  · rintro ⟨_,⟨q,rfl⟩,rfl⟩
    exact ⟨_,⟨leftChange q,rfl⟩,(movement_left_original m q).symm⟩
  · rintro ⟨_,⟨q,rfl⟩,rfl⟩
    obtain ⟨r,rfl⟩ := leftChange_bijective.surjective q
    exact ⟨_,⟨r,rfl⟩,movement_left_original m r⟩

theorem movement_rightFactor : rightFactor.map movement = M12SmallPair.rightFactor.map m.embedding := by
  ext x
  constructor
  · rintro ⟨_,⟨q,rfl⟩,rfl⟩
    exact ⟨_,⟨rightChange q,rfl⟩,(movement_right_original m q).symm⟩
  · rintro ⟨_,⟨q,rfl⟩,rfl⟩
    obtain ⟨r,rfl⟩ := rightChange_bijective.surjective q
    exact ⟨_,⟨r,rfl⟩,movement_right_original m r⟩

theorem movement_core : QK.map movement = M12SmallPair.core.map m.embedding := by
  rw [QK, Subgroup.map_sup, movement_leftFactor m, movement_rightFactor m, ← Subgroup.map_sup]
  rfl

end Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
