module

public import Theory.Mathieu.M23.Properties.Transitivity
public import Theory.Mathieu.M23.Properties.Simplicity
public import Theory.Mathieu.M23.Block
public import Theory.Mathieu.M24.Properties.Order

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

private noncomputable def m23M24PointMulActionHom :
    Fin 23 →ₑ[m23SimplicityExtendEquiv.toMonoidHom]
      SubMulAction.ofStabilizer M24 (24 : Fin 24) where
  toFun := m23PointEquiv
  map_smul' g i := by
    apply Subtype.ext
    change
      m23PointEmbedding ((g : Equiv.Perm (Fin 23)) i) =
        m23ExtendHom g (m23PointEmbedding i)
    exact (m23ExtendHom_apply_embedded g i).symm

private theorem m24PointStabilizer_isFourPretransitive :
    MulAction.IsMultiplyPretransitive
      (MulAction.stabilizer M24 (24 : Fin 24))
      (SubMulAction.ofStabilizer M24 (24 : Fin 24)) 4 := by
  exact
    (MulAction.IsPretransitive.of_embedding_congr
      (f := m23M24PointMulActionHom)
      m23SimplicityExtendEquiv.surjective
      m23PointEquiv.bijective).mp
      m23_isFourPretransitive

/-- The natural degree-24 action of M24 is five-transitive. -/
public theorem m24_isFivePretransitive :
    MulAction.IsMultiplyPretransitive M24 (Fin 24) 5 := by
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive
    (G := M24) (α := Fin 24) (a := (24 : Fin 24)) (n := 4)).2
  exact m24PointStabilizer_isFourPretransitive

end Sporadic.Mathieu
