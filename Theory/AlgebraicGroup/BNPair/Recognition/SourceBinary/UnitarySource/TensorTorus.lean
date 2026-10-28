module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanPinning
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.LinearIrreducibility
public import Theory.Representation.SL2.BinarySmallModels

/-!
# The smaller source root excludes the natural module

Every nonzero vector of the natural binary SL₂(F) module has a free
orbit under its split torus. The actual aligned torus lies in the full
source Cartan, which normalizes the other simple root inside the
complementary section. A natural realization would therefore inject
Fˣ into that smaller root. In the U₄ row its order is q, while
|Fˣ| = q²−1 > q, including q=2.

The representation below is literal conjugation on the same remainder,
with the whole rank-one pinning aligned to the specified source reflection.
TensorRecognition uses the orbit bound to select the Hermitian branch
of the proved binary SL₂ classifier, without a module-identification input.

Source: Fong--Seitz I (4C), (6A)(b), pp.20--21,37--38;
II (8B), p.201 (the three Cartan constituents).
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
open Theory.PSL2.SemilinearCoverage
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

omit [Finite F] in
/-- A nonzero natural vector has a free split-torus orbit. -/
theorem natural_torus_orbit_injective (v : Fin 2 → F) (hv : v ≠ 0) :
    Function.Injective (fun a : Fˣ => Representation.SL2.BinarySmall.natural (tor a) v) := by
  intro a b hab
  have hv' : ∃ j, v j ≠ 0 := Function.ne_iff.mp hv
  obtain ⟨j,hj⟩ := hv'
  have he := congrFun hab j
  change (tor a).val.mulVec v j = (tor b).val.mulVec v j at he
  fin_cases j
  · apply Units.ext
    apply mul_right_cancel₀ hj
    simpa [tor, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using he
  · apply inv_injective
    apply Units.ext
    apply mul_right_cancel₀ hj
    simpa [tor, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using he

open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
  [IsElementaryAbelian 2 (simpleRemainder Q split i)]
  (μ : localGroup Q split i ≃* PSL(2,F)) (s : RootReflection Q split i)

/-- Literal conjugation by the entire reflection-aligned root actor. -/
def alignedRemainderRepresentation :
    Representation (ZMod 2) SL(2,F) (Additive (simpleRemainder Q split i)) :=
  (elementaryRepresentation (p := 2) (remainderRankOneAction Q split i hV)).comp
    (alignedPinning Q split i hV μ s).toMonoidHom

/-- A natural realization forces a large orbit in the other actual simple root. -/
theorem natural_remainder_torus_bound (j : Fin 2) (hij : i ≠ j)
    (hnatural : Representation.SL2.BinarySmall.IsNatural
      (alignedRemainderRepresentation Q split i hV μ s)) :
    Nat.card F - 1 ≤ Nat.card (simpleRoot Q split j) := by
  obtain ⟨e⟩ := hnatural
  obtain ⟨x,hx1⟩ : ∃ x : simpleRoot Q split j, x ≠ 1 := (Subgroup.ne_bot_iff_exists_ne_one).mp (simpleRoot_ne_bot Q split j)
  let v : Additive (simpleRemainder Q split i) :=
    .ofMul ⟨x,(opposite_roots_le_remainder Q split j i hij.symm).1 x.property⟩
  have hv : e v ≠ 0 := by
    intro hz
    have h := e.injective (hz.trans (map_zero e).symm)
    apply hx1
    apply Subtype.ext
    exact (congrArg (fun w : Additive (simpleRemainder Q split i) => (w.toMul : X ⧸ Q.D)) h)
  let f : Fˣ → simpleRoot Q split j := fun a =>
    ⟨alignedTorus Q split i hV μ s a * x * (alignedTorus Q split i hV μ s a)⁻¹,
      (mem_normalizer_iff.mp (torus_normalizes_simpleRoot Q split j
        (alignedTorus_mem_cartan Q split i hV μ s a)) x).mp x.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply natural_torus_orbit_injective (e v) hv
    have he (a : Fˣ) :
        e (alignedRemainderRepresentation Q split i hV μ s (tor a) v) =
          Representation.SL2.BinarySmall.natural (tor a) (e v) :=
      LinearMap.congr_fun (e.isIntertwining' (tor a)) v
    dsimp only
    rw [← he a, ← he b]
    congr 1
    simp only [alignedRemainderRepresentation, MonoidHom.comp_apply, elementaryRepresentation_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    simpa only [toMul_ofMul, remainderRankOneAction_apply,
      MulEquiv.coe_toMonoidHom, alignedPinning_coe, v, f, alignedTorus] using
      congrArg Subtype.val hab
  simpa only [Nat.card_units] using Nat.card_le_card_of_injective f hf

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
