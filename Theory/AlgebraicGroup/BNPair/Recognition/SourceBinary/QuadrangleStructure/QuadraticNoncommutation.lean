module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.LinearIrreducibility
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FourCartanOrders

/-!
# Noncommuting roots forced by the elementary quadratic radical

The actual simple reflection moves the opposite root to its disjoint crossed
root inside the same complementary section. Thus the full root-generated
actor acts nontrivially, before any nonzero commutator is known. If this
section is elementary and has the minimum order for its binary SL₂ actor,
the minimum-degree bound makes the action irreducible and its fixed space
zero. Commuting same-type roots would make the full actor centralize the
nontrivial crossed root, contradicting that fixed-space calculation.

This removes the nonabelian opposite-core premise from the quadratic U₄
source recognition. The source adapter constructs the actor and section
order from the original factor quotients. Both orientations and SL₂(4),
whose opposite factor can be SL₂(2), are included. No perfectness is imposed
on the opposite factor, and every action takes place in the same quotient.

Source: Fong--Seitz I (3G), (4B), (6A)(b), pp.14--16,19--22,37--38;
DGS, Groups and Graphs (1985), (11.7), pp.174--175. This is a proof of a
needed premise at the elementary quadratic profile, not exhaustive selection.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The reflection moves the opposite root inside the actual radical. -/
theorem remainder_action_moves_root (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    ∃ r, remainderRankOneAction Q split i hV r ≠ 1 := by
  by_contra! hh
  apply simpleRoot_ne_bot Q split j
  apply _root_.eq_bot_iff.mpr
  intro a ha
  let s := UnitarySource.actorReflection Q split i
  let r : rankOne Q split i := ⟨s.val,s.mem_rankOne⟩
  let v : simpleRemainder Q split i :=
    ⟨a,(opposite_roots_le_remainder Q split j i hij.symm).1 ha⟩
  have he := congrArg (fun f : MulAut (simpleRemainder Q split i) =>
    (f v : X ⧸ Q.D)) (hh r⁻¹)
  change (s.val : X ⧸ Q.D)⁻¹*a*((s.val : X ⧸ Q.D)⁻¹)⁻¹ = a at he
  rw [inv_inv] at he
  have hac : a ∈ rootAt Q split j (Q.simple i) := by
    rw [rootAt_eq Q split j (Q.simple i) s.val s.class_eq,←he,rightConjugate]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*(s.val : X ⧸ Q.D))*(s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using ha
  exact (disjoint_iff.mp (simpleRoot_disjoint_remainder Q split j)).le
    ⟨ha,cross_root_le_own_remainder Q split hm j i hij.symm hac⟩

/-- Minimal degree forces a nonzero crossed-root commutator, without assuming
nonabelianity of the opposite radical. -/
theorem quadratic_elementary_cross_nonzero {F : Type*}
    [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    [IsElementaryAbelian 2 (simpleRemainder Q split i)]
    (μ : rankOne Q split i ≃* SL(2,F)) {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n)
    (hcard : Nat.card (simpleRemainder Q split i) = Nat.card F ^ 2) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ ≠ ⊥ := by
  let φ := remainderRankOneAction Q split i hV
  let ρ := (elementaryRepresentation (p := 2) φ).comp μ.symm.toMonoidHom
  have hntρ : ∃ g, ρ g ≠ 1 := by
    obtain ⟨a,ha⟩ := remainder_action_moves_root Q split hm i j hij hV
    refine ⟨μ a,fun he => ha ?_⟩
    ext v : 1
    have hv := congrArg (fun f : Module.End (ZMod 2) (Additive (simpleRemainder Q split i)) =>
      f (Additive.ofMul v)) he
    change Additive.ofMul (φ (μ.symm (μ a)) v) = Additive.ofMul v at hv
    change φ a v = v
    simpa only [MulEquiv.symm_apply_apply] using Additive.ofMul.injective hv
  have hd : Module.finrank (ZMod 2) (Additive (simpleRemainder Q split i)) = 2*n := by
    have hc : Nat.card (simpleRemainder Q split i) =
        2 ^ Module.finrank (ZMod 2) (Additive (simpleRemainder Q split i)) := by
      change Nat.card (Additive (simpleRemainder Q split i)) = _
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (simpleRemainder Q split i)))
    rw [hc,hF,←pow_mul] at hcard
    have he := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hcard
    omega
  have hl := Representation.SL2.fixedCodim_top_lower ρ hntρ hn hF
  have he := fixedCodim_add_finrank ρ ⊤
  have hz : fixedSpace ρ ⊤ = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  intro hzero
  have hcent := UnitarySource.rankOne_centralizes_cross_root Q split hm i j hij hzero
  have hbot : rootAt Q split i (Q.simple j) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro a ha
    let v : simpleRemainder Q split i :=
      ⟨a,cross_root_le_own_remainder Q split hm i j hij ha⟩
    have hv : Additive.ofMul v ∈ fixedSpace ρ ⊤ := by
      intro g
      change Additive.ofMul (φ (μ.symm g.val) v) = Additive.ofMul v
      apply congrArg Additive.ofMul
      apply Subtype.ext
      rw [remainderRankOneAction_apply]
      have hc := mem_centralizer_iff.mp (hcent (μ.symm g.val).property) a ha
      exact mul_inv_eq_iff_eq_mul.mpr hc.symm
    rw [hz,Submodule.mem_bot] at hv
    exact congrArg (fun x : Additive (simpleRemainder Q split i) => (x.toMul : X ⧸ Q.D)) hv
  rw [rootAt,rightConjugate,comap_equiv_eq_map_symm'] at hbot
  exact simpleRoot_ne_bot Q split i
    ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).symm.injective).mp hbot)

/-- The same elementary section is irreducible before a crossed-root
commutator is supplied. -/
theorem quadratic_elementary_remainder_irreducible {F : Type*}
    [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    [IsElementaryAbelian 2 (simpleRemainder Q split i)]
    (μ : rankOne Q split i ≃* SL(2,F)) {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n)
    (hcard : Nat.card (simpleRemainder Q split i) = Nat.card F ^ 2) :
    (elementaryRepresentation (p := 2)
      (remainderRankOneAction Q split i hV)).IsIrreducible :=
  minimal_linear_action_irreducible μ (remainderRankOneAction Q split i hV)
    (remainder_action_moves_root Q split hm i j hij hV) hn hF hcard

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
