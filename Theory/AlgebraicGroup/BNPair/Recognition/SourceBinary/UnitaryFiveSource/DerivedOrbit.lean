module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorTorus
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryLinearActions
public import Theory.Representation.SL2.AutomorphismNatural

/-!
# The actual small root layer excludes a natural derived module

The nonzero derived subgroup of the opposite unitary root lies in the
linear radical's derived layer. The full linear rank-one torus normalizes
it. Every nonzero vector in a natural SL₂ module has a free torus orbit,
including after an arbitrary automorphism of the actor. Consequently a
natural realization would force at least |K| - 1 elements into that root
layer, whose order is at most the fixed-field order in the U₅ branch.

The representation retains the specified full SL₂ marking; the reflection
pinning is used only to construct the actual torus orbit. There is no
actor-automorphism or natural-action premise in the later source theorem.
Source: Fong--Seitz II (8C), p.206, the Hermitian action in (8.21).
Consumer: UnitaryFiveSource.DerivedHermitian constructs the intertwiner on
the literal radical-derived subgroup, including fixed-field orders 2 and 4.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
open Theory.PSL2.SemilinearCoverage
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

private theorem twisted_natural_torus_injective (α : MulAut SL(2,F))
    (v : Fin 2 → F) (hv : v ≠ 0) :
    Function.Injective (fun a : Fˣ => SL2.BinarySmall.natural (α (tor a)) v) := by
  have hw : SL2AutomorphismNatural.action α.symm v ≠ 0 := by
    intro hz
    exact hv ((SL2AutomorphismNatural.action.apply_bijective α.symm).injective
      (hz.trans (map_zero _).symm))
  intro a b hab
  apply UnitarySource.natural_torus_orbit_injective _ hw
  have h := congrArg (SL2AutomorphismNatural.action α.symm) hab
  simpa only [SL2.BinarySmall.natural_apply, SL2AutomorphismNatural.action_intertwines,
    MulEquiv.symm_apply_apply] using h

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
  [IsElementaryAbelian 2
    (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))]
  (μ : rankOne Q split i ≃* SL(2,F))

/-- Conjugation on the actual derived layer, with the specified linear actor. -/
def linearDerivedRepresentation : Representation (ZMod 2) SL(2,F)
    (Additive (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))) :=
  (elementaryRepresentation (p := 2) (remainderDerivedAction Q split i hV)).comp
    μ.symm.toMonoidHom

/-- A natural model would inject the whole linear torus into the opposite root-derived layer. -/
theorem natural_derived_torus_bound (s : RootReflection Q split i)
    (j : Fin 2) (hij : i ≠ j)
    (hne : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ≠ ⊥)
    (hnatural : SL2.BinarySmall.IsNatural (linearDerivedRepresentation Q split i hV μ)) :
    Nat.card F - 1 ≤ Nat.card (⁅simpleRoot Q split j,simpleRoot Q split j⁆ : Subgroup (X ⧸ Q.D)) := by
  let ξ := (localGroupEquivOfCenterless Q split i hV μ
    Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans
      Atlas.RankOneFieldAutomorphisms.slEquivPSL
  let pin := alignedPinning Q split i hV ξ s
  let α : MulAut SL(2,F) := pin.trans μ
  obtain ⟨e⟩ := hnatural
  obtain ⟨x,hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hRV := (opposite_roots_le_remainder Q split j i hij.symm).1
  let v : Additive (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) :=
    .ofMul ⟨x,commutator_mono hRV hRV x.property⟩
  have hv : e v ≠ 0 := by
    intro hz
    have he := e.injective (hz.trans (map_zero e).symm)
    apply hx1
    apply Subtype.ext
    exact congrArg (fun w : Additive (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
      Subgroup (X ⧸ Q.D)) => (w.toMul : X ⧸ Q.D)) he
  have hnorm (a : Fˣ) : alignedTorus Q split i hV ξ s a ∈
      normalizer ((⁅simpleRoot Q split j,simpleRoot Q split j⁆ : Subgroup (X ⧸ Q.D)) : Set _) := by
    rw [←map_subtype_commutator]
    exact normalizer_le_normalizer_characteristic_image (simpleRoot Q split j)
      (_root_.commutator _) (torus_normalizes_simpleRoot Q split j
        (alignedTorus_mem_cartan Q split i hV ξ s a))
  let f : Fˣ → (⁅simpleRoot Q split j,simpleRoot Q split j⁆ : Subgroup (X ⧸ Q.D)) :=
    fun a => ⟨alignedTorus Q split i hV ξ s a * x * (alignedTorus Q split i hV ξ s a)⁻¹,
      (mem_normalizer_iff.mp (hnorm a) x).mp x.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply twisted_natural_torus_injective α (e v) hv
    have he (a : Fˣ) : e (linearDerivedRepresentation Q split i hV μ (α (tor a)) v) =
        SL2.BinarySmall.natural (α (tor a)) (e v) :=
      LinearMap.congr_fun (e.isIntertwining' _) v
    dsimp only
    rw [←he a,←he b]
    congr 1
    simp only [linearDerivedRepresentation,MonoidHom.comp_apply,elementaryRepresentation_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    simpa only [α,MulEquiv.trans_apply,MulEquiv.symm_apply_apply,toMul_ofMul,
      remainderDerivedAction_apply,MulEquiv.coe_toMonoidHom,alignedPinning_coe,
      pin,v,f,alignedTorus] using congrArg Subtype.val hab
  simpa only [Nat.card_units] using Nat.card_le_card_of_injective f hf

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
