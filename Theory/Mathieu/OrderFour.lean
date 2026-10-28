module

public import Theory.Mathieu.M12.Properties.PointStabilizer
public import Theory.Mathieu.M23.Properties.Simplicity

/-!
# Order-four elements in the native Mathieu groups

The checked M₁₁ and M₂₂ generators already have order four. The actual
point-stabilizer embeddings carry them to M₁₂, M₂₃ and M₂₄. Thus these
witnesses require no new finite enumeration or abstract family identification.

Consumer: the binary SL₂-section obstruction in Aschbacher--Smith 4.4.12,
printed pp.621--622. The imported generator and point-stabilizer files retain
the ATLAS and Witt-design source references.
-/

public noncomputable section
open Subgroup
namespace Sporadic.Mathieu

private theorem exists_order_four_map {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Injective f) (h : ∃ x : X, orderOf x = 4) :
    ∃ y : Y, orderOf y = 4 := by
  obtain ⟨x,hx⟩ := h
  exact ⟨f x, (orderOf_injective f hf x).trans hx⟩

/-- An order-four element inherited from the actual M₁₁ point stabilizer. -/
theorem m12_exists_order_four : ∃ x : M12, orderOf x = 4 := by
  let f : M11 →* M12 :=
    (MulAction.stabilizer M12 (12 : Fin 12)).subtype.comp m11ToM12PointStabilizer
  apply exists_order_four_map f
    (Subtype.val_injective.comp m11ToM12PointStabilizer_injective)
  exact ⟨⟨m11GeneratorB,m11GeneratorB_mem⟩,
    (Subgroup.orderOf_coe _).symm.trans m11GeneratorB_order⟩

/-- An order-four element inherited from the actual native degree-22 generator. -/
theorem m22_exists_order_four : ∃ x : M22, orderOf x = 4 :=
  ⟨⟨m22GeneratorB,m22GeneratorB_mem_M22⟩,
    (Subgroup.orderOf_coe _).symm.trans m22GeneratorB_order⟩

/-- An order-four element inherited from the actual M₂₂ point stabilizer. -/
theorem m23_exists_order_four : ∃ x : M23, orderOf x = 4 := by
  let f : M22 →* M23 := (MulAction.stabilizer M23 (9 : Fin 23)).subtype.comp
    m23EquivM22PointStabilizer.toMonoidHom
  exact exists_order_four_map f
    (Subtype.val_injective.comp m23EquivM22PointStabilizer.injective) m22_exists_order_four

/-- An order-four element inherited from the actual M₂₃ point stabilizer. -/
theorem m24_exists_order_four : ∃ x : M24, orderOf x = 4 := by
  let f : M23 →* M24 :=
    (MulAction.stabilizer M24 (24 : Fin 24)).subtype.comp m23ToM24PointStabilizer
  exact exists_order_four_map f
    (Subtype.val_injective.comp m23ToM24PointStabilizer_injective) m23_exists_order_four

end Sporadic.Mathieu
