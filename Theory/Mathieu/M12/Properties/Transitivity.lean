module

public import Theory.Mathieu.M11.Properties.Transitivity
public import Theory.Mathieu.M12.Properties.Order

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

open Theory.GroupTheory

namespace Sporadic.Mathieu

private noncomputable def m11M12PointMulActionHom :
    Fin 11 →ₑ[m11ToM12PointStabilizer]
      SubMulAction.ofStabilizer M12 (12 : Fin 12) where
  toFun := m11M12PointEquiv
  map_smul' g i := by
    apply Subtype.ext
    change
      m11M12PointEmbedding ((g : Equiv.Perm (Fin 11)) i) =
        m11ToM12ExtendHom g (m11M12PointEmbedding i)
    exact (m11ToM12ExtendHom_apply_embedded g i).symm

private theorem m12PointStabilizer_isFourPretransitive :
    MulAction.IsMultiplyPretransitive
      (MulAction.stabilizer M12 (12 : Fin 12))
      (SubMulAction.ofStabilizer M12 (12 : Fin 12)) 4 := by
  have hSurj : Function.Surjective m11ToM12PointStabilizer :=
    (m11ToM12PointStabilizer_injective.bijective_of_nat_card_le (by
      exact (Nat.card_congr m11EquivM12PointStabilizer.toEquiv).ge)).surjective
  exact
    (MulAction.IsPretransitive.of_embedding_congr
      (f := m11M12PointMulActionHom)
      hSurj
      m11M12PointEquiv.bijective).mp
      m11_isFourPretransitive

/-- The natural degree-12 action of M12 is five-transitive. -/
public theorem m12_isFivePretransitive :
    MulAction.IsMultiplyPretransitive M12 (Fin 12) 5 := by
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive
    (G := M12) (α := Fin 12) (a := (12 : Fin 12)) (n := 4)).2
  exact m12PointStabilizer_isFourPretransitive

private def m12FivePointBase : Fin 5 ↪ Fin 12 :=
  Fin.castAddEmb 7

private theorem m12_fivePointOrbitMap_bijective :
    Function.Bijective (fun g : M12 => g • m12FivePointBase) := by
  have hSurj : Function.Surjective (fun g : M12 => g • m12FivePointBase) := by
    intro y
    exact
      (MulAction.isMultiplyPretransitive_iff.mp m12_isFivePretransitive)
        m12FivePointBase y
  apply (Nat.bijective_iff_surjective_and_card _).2
  refine ⟨hSurj, ?_⟩
  calc
    Nat.card M12 = 95040 := m12_order
    _ = Fintype.card (Fin 5 ↪ Fin 12) := by
      rw [Fintype.card_embedding_eq]
      norm_num [Nat.descFactorial]
    _ = Nat.card (Fin 5 ↪ Fin 12) := Nat.card_eq_fintype_card.symm

/-- The natural degree-12 action of M12 is sharply five-transitive. -/
public theorem m12_isSharplyFivePretransitive :
    Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive M12 (Fin 12) 5 :=
  Theory.GroupTheory.MulAction.isSharplyMultiplyPretransitive_of_bijective_orbitMap
    m12FivePointBase m12_fivePointOrbitMap_bijective


open scoped Pointwise

/-- Every element of `M12` preserves the concrete 132 hexads of `W12` setwise. -/
public theorem m12_preserves_hexads_set (g : M12) :
    ((g : M12) : Equiv.Perm (Fin 12)) •
        (m12Blocks : Set (Finset (Fin 12))) =
      (m12Blocks : Set (Finset (Fin 12))) :=
  (mem_M12_iff ((g : M12) : Equiv.Perm (Fin 12))).mp g.property

/-- Every element of `M12` permutes the finite hexad table. -/
public theorem m12_preserves_hexads (g : M12) :
    ((g : M12) : Equiv.Perm (Fin 12)) • m12Blocks = m12Blocks := by
  apply Finset.coe_injective
  simpa only [Finset.coe_smul_finset] using m12_preserves_hexads_set g

/-- The natural action of `M12` is by automorphisms of the Witt design `W12`. -/
public theorem m12_preserves_witt_design (g : M12) :
    ((g : M12) : Equiv.Perm (Fin 12)) •
        (m12WittDesign.blocks : Set (Finset (Fin 12))) =
      (m12WittDesign.blocks : Set (Finset (Fin 12))) := by
  simpa only [m12WittDesign, SteinerSystem.ofPairwiseIntersection_blocks] using
    m12_preserves_hexads_set g

/-- The point-12 stabilizer, identified with `M11`, is maximal in `M12`. -/
public theorem m12PointStabilizerTwelve_isCoatom :
    IsCoatom (MulAction.stabilizer M12 (12 : Fin 12)) := by
  let : MulAction.IsMultiplyPretransitive M12 (Fin 12) 5 :=
    m12_isFivePretransitive
  have htwo : MulAction.IsMultiplyPretransitive M12 (Fin 12) 2 :=
    MulAction.isMultiplyPretransitive_of_le
      (G := M12) (α := Fin 12) (m := 2) (n := 5) (by norm_num) (by norm_num)
  let : MulAction.IsPreprimitive M12 (Fin 12) :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo
  exact
    MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
      M12 (12 : Fin 12)

/-- The point-12 stabilizer has order `7920`, hence is isomorphic to `M11`. -/
public theorem m12PointStabilizerTwelve_card :
    Nat.card (MulAction.stabilizer M12 (12 : Fin 12)) = 7920 := by
  calc
    Nat.card (MulAction.stabilizer M12 (12 : Fin 12)) = Nat.card M11 :=
      Nat.card_congr m11EquivM12PointStabilizer.symm.toEquiv
    _ = 7920 := m11_order

end Sporadic.Mathieu
