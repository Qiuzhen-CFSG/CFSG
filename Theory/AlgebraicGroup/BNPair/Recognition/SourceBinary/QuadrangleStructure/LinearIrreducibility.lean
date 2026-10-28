module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.TorusIrreducibility
public import Theory.Representation.SL2.FullFixedIndex
public import Theory.Representation.SL2.MinimalBinaryDegree
public import Theory.Representation.ElementaryPerfectSplit
/-!
# The irreducible complementary section in the quadratic linear quadrangle

The full root-generated actor acts by conjugation on the literal
complementary section. Its nontrivial opposite-root commutator makes
this action nontrivial. The section has order |K|², where the larger
binary field K has degree at least two. The checked minimum-degree
bound for binary SL₂ makes its fixed space zero and then forces a
simple submodule to fill the whole section. This proves irreducibility
without choosing tensor coordinates or compatible field labels.

The minimum actor is SL₂(4), so the source fixed field of order two is
included. No perfectness is imposed on the smaller local actor SL₂(2).
The CFSG QuadraticIrreducibility application supplies the full actor,
section order and nonzero commutator from the same original DGS profile.

Source: Fong--Seitz I (4B), (6A)(b), pp.19--22,37--38;
DGS (11.7), pp.174--175.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
private theorem minimal_linear_irreducible {F V : Type*}
    [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,F) V) (hnt : ∃ g, ρ g ≠ 1)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hd : Module.finrank (ZMod 2) V ≤ 2*n) : ρ.IsIrreducible := by
  have hl := Representation.SL2.fixedCodim_top_lower ρ hnt hn hF
  have he := fixedCodim_add_finrank ρ ⊤
  have hz : fixedSpace ρ ⊤ = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have hi : ρ.invariants = ⊥ := by
    convert hz using 1
    ext v
    change (∀ g, ρ g v = v) ↔ ∀ g : (⊤ : Subgroup SL(2,F)), ρ g v = v
    exact ⟨fun hh g => hh g, fun hh g => hh ⟨g,mem_top g⟩⟩
  have hp : 0 < Module.finrank (ZMod 2) V := by omega
  let : Nontrivial V := Module.nontrivial_of_finrank_pos hp
  exact Representation.SL2.irreducible_of_fixed_free_minimal_binary_degree ρ hi (by omega) hF hd

/-- Minimal-order binary linear actions are irreducible, including the actor SL2(4). -/
theorem minimal_linear_action_irreducible {F A R : Type*}
    [Field F] [Finite F] [CharP F 2] [Group A] [Group R] [Finite R]
    [IsElementaryAbelian 2 R]
    (μ : A ≃* SL(2,F)) (φ : A →* MulAut R)
    (hnt : ∃ a, φ a ≠ 1) {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) (hR : Nat.card R = Nat.card F ^ 2) :
    (elementaryRepresentation (p := 2) φ).IsIrreducible := by
  let ρ := elementaryRepresentation (p := 2) φ
  let σ := ρ.comp μ.symm.toMonoidHom
  have hd : Module.finrank (ZMod 2) (Additive R) = 2*n := by
    have hc : Nat.card R = 2 ^ Module.finrank (ZMod 2) (Additive R) := by
      change Nat.card (Additive R) = _
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive R))
    rw [hc,hF,←pow_mul] at hR
    have he := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hR
    omega
  have hntσ : ∃ g, σ g ≠ 1 := by
    obtain ⟨a,ha⟩ := hnt
    refine ⟨μ a,fun he => ha ?_⟩
    ext v
    have hv := congrArg (fun f : Module.End (ZMod 2) (Additive R) => f (Additive.ofMul v)) he
    change Additive.ofMul (φ (μ.symm (μ a)) v) = Additive.ofMul v at hv
    change φ a v = v
    simpa only [MulEquiv.symm_apply_apply] using Additive.ofMul.injective hv
  exact (irreducible_comp_surjective_iff μ.symm.toMonoidHom μ.symm.surjective ρ).mp
    (minimal_linear_irreducible σ hntσ hn hF hd.le)

open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Conjugation by the full root-generated actor on the same complementary section. -/
@[expose] def remainderRankOneAction (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    rankOne Q split i →* MulAut (simpleRemainder Q split i) :=
  (simpleRemainder Q split i).normalizerMonoidHom.comp
    (inclusion ((rankOne_le_parabolic Q split i).trans
      (remainder_parabolic_normalizes Q split i hV)))

@[simp] theorem remainderRankOneAction_apply (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (r : rankOne Q split i) (v : simpleRemainder Q split i) :
    (remainderRankOneAction Q split i hV r v : X ⧸ Q.D) =
      (r : X ⧸ Q.D)*v*(r : X ⧸ Q.D)⁻¹ := rfl

/-- The exact U4 opposite-root commutator forces the actor action to be nontrivial. -/
theorem remainderRankOneAction_nontrivial (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (hcomm : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
      rootAt Q split j (Q.simple i)) :
    ∃ r, remainderRankOneAction Q split i hV r ≠ 1 := by
  by_contra! hh
  have hc : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro a ha
    apply mem_centralizer_iff.mpr
    intro v hv
    let r : rankOne Q split i := ⟨a,(show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left) ha⟩
    let w : simpleRemainder Q split i :=
      ⟨v,cross_root_le_own_remainder Q split hm i j hij hv⟩
    have he := congrArg (fun f : MulAut (simpleRemainder Q split i) =>
      (f w : X ⧸ Q.D)) (hh r)
    change a*v*a⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  rw [hcomm,rootAt,rightConjugate,comap_equiv_eq_map_symm'] at hc
  exact simpleRoot_ne_bot Q split j
    ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).symm.injective).mp hc)

/-- Irreducibility of the full U4 complementary section under its FULL larger actor. -/
theorem quadratic_remainder_irreducible {F : Type*}
    [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    [IsElementaryAbelian 2 (simpleRemainder Q split i)]
    (μ : rankOne Q split i ≃* SL(2,F)) {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n)
    (hcard : Nat.card (simpleRemainder Q split i) = Nat.card F ^ 2)
    (hcomm : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
      rootAt Q split j (Q.simple i)) :
    (elementaryRepresentation (p := 2) (remainderRankOneAction Q split i hV)).IsIrreducible :=
  minimal_linear_action_irreducible μ (remainderRankOneAction Q split i hV)
    (remainderRankOneAction_nontrivial Q split hm i j hij hV hcomm) hn hF hcard

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
