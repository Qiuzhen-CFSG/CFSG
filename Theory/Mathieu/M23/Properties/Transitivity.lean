module

public import Theory.Mathieu.M22.Properties.Transitivity
public import Theory.Mathieu.M23.Properties.Simplicity

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

private noncomputable def m22M23PointEquivForTransitivity :
    Fin 22 ≃ SubMulAction.ofStabilizer M23 (9 : Fin 23) where
  toFun i := ⟨m22M23PointMap i, m22M23PointMap_ne_nine i⟩
  invFun x := m22M23PointMapLeftInverse x.1
  left_inv := m22M23PointMap_leftInverse
  right_inv := by
    intro x
    apply Subtype.ext
    exact m22M23PointMap_rightInverse_of_ne_nine x.1 x.2

private noncomputable def m22M23PointMulActionHom :
    Fin 22 →ₑ[m23EquivM22PointStabilizer.toMonoidHom]
      SubMulAction.ofStabilizer M23 (9 : Fin 23) where
  toFun := m22M23PointEquivForTransitivity
  map_smul' g i := by
    apply Subtype.ext
    dsimp only [m22M23PointEquivForTransitivity]
    change
      m22M23PointMap ((g : Equiv.Perm (Fin 22)) i) =
        m22M23RelabelHom (g : Equiv.Perm (Fin 22)) (m22M23PointMap i)
    symm
    change
      (Equiv.Perm.viaEmbeddingHom m22M23PointEmbedding
        (g : Equiv.Perm (Fin 22))) (m22M23PointEmbedding i) =
        m22M23PointEmbedding ((g : Equiv.Perm (Fin 22)) i)
    rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply]

private theorem m23PointStabilizer_isThreePretransitive :
    MulAction.IsMultiplyPretransitive
      (MulAction.stabilizer M23 (9 : Fin 23))
      (SubMulAction.ofStabilizer M23 (9 : Fin 23)) 3 := by
  exact
    (MulAction.IsPretransitive.of_embedding_congr
      (f := m22M23PointMulActionHom)
      m23EquivM22PointStabilizer.surjective
      m22M23PointEquivForTransitivity.bijective).mp
      m22_isThreePretransitive

/-- The natural degree-23 action of M23 is four-transitive. -/
public theorem m23_isFourPretransitive :
    MulAction.IsMultiplyPretransitive M23 (Fin 23) 4 := by
  let : MulAction.IsPretransitive M23 (Fin 23) := m23_isPretransitive
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive
    (G := M23) (α := Fin 23) (a := (9 : Fin 23)) (n := 3)).2
  exact m23PointStabilizer_isThreePretransitive

end Sporadic.Mathieu
