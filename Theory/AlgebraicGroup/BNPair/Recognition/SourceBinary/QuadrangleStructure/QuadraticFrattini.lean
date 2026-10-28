module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.QuadraticNoncommutation
public import Theory.GroupAction.PerfectFrattiniAction
public import GorensteinWalter.SL2ProjectiveCover

/-!
# The elementary radical forced by quadratic linear root orders

A nontrivial action of SL₂(2ⁿ), n > 1, on a two-group of order 2^(2n)
forces that two-group to be elementary abelian. Perfectness and Burnside's
Frattini automorphism-kernel theorem preserve the nontrivial action on the
Frattini quotient. The minimum binary degree is 2n, so this quotient already
has the order of the whole group and the Frattini subgroup is trivial.

In a split quadrangle the simple reflection moves the opposite root inside
the same complementary section. This supplies the nontrivial action without
assuming an elementary radical or a nonzero crossed-root commutator. The
original-factor adapter computes the required order from the two panel
indices and transports the result back through the literal endpoint map.
It removes the elementary-core premise from the quadratic U₄ branch,
including the smallest larger actor SL₂(4). The opposite actor need not be
perfect. No rank-two classification is used in this argument.

Source: Burnside's basis theorem; Fong--Seitz I (4B), (6A)(b),
pp.19--22,37--38; DGS, Groups and Graphs (1985), (11.7), pp.174--175.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure

private theorem minimal_linear_two_group_elementary {F A V : Type*}
    [Field F] [Finite F] [CharP F 2] [Group A] [Group V] [Finite V]
    (μ : A ≃* SL(2,F)) (hp : IsPGroup 2 V) (φ : A →* MulAut V)
    (hnt : ∃ a, φ a ≠ 1) {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) (hcard : Nat.card V = Nat.card F ^ 2) :
    IsElementaryAbelian 2 V := by
  have hfour : 3 < Nat.card F := by
    rw [hF]
    have hh : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  let : Group.IsPerfect SL(2,F) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hfour
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := μ.symm.toMonoidHom) μ.symm.surjective
  let : Fact (IsPGroup 2 V) := ⟨hp⟩
  let W := V ⧸ frattini V
  let : IsElementaryAbelian 2 W := isElementaryAbelian_quotient_frattini
  let β := (quotientAut (frattini V)).comp φ
  have hβ : β ≠ 1 := φ.frattini_comp_ne_one_of_isPerfect hp (by
    intro he
    obtain ⟨a,ha⟩ := hnt
    exact ha (DFunLike.congr_fun he a))
  have hntβ : ∃ a, β a ≠ 1 := by
    by_contra! hh
    exact hβ (MonoidHom.ext hh)
  let ρ := (elementaryRepresentation (p := 2) β).comp μ.symm.toMonoidHom
  have hntρ : ∃ g, ρ g ≠ 1 := by
    obtain ⟨a,ha⟩ := hntβ
    refine ⟨μ a,fun he => ha ?_⟩
    ext v : 1
    have hv := congrArg (fun f : Module.End (ZMod 2) (Additive W) =>
      f (Additive.ofMul v)) he
    change Additive.ofMul (β (μ.symm (μ a)) v) = Additive.ofMul v at hv
    change β a v = v
    simpa only [MulEquiv.symm_apply_apply] using Additive.ofMul.injective hv
  have hl := Representation.SL2.fixedCodim_top_lower ρ hntρ hn hF
  have hd := fixedCodim_add_finrank ρ ⊤
  change fixedCodim ρ ⊤ + Module.finrank (ZMod 2) (fixedSpace ρ ⊤) =
    Module.finrank (ZMod 2) (Additive W) at hd
  have hc : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    change Nat.card (Additive W) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W))
  have hlow : Nat.card F ^ 2 ≤ Nat.card W := by
    rw [hc,hF,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini V)
  have hpos : 0 < Nat.card W := Nat.card_pos
  have hposΦ : 0 < Nat.card (frattini V) := Nat.card_pos
  have hΦ : Nat.card (frattini V) = 1 := by
    change Nat.card V = Nat.card W * Nat.card (frattini V) at hprod
    rw [hcard] at hprod
    nlinarith
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp (card_eq_one.mp hΦ)

open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The quadratic-size radical is elementary before any core-structure
or crossed-root commutator premise is supplied. -/
theorem quadratic_remainder_elementary {F : Type*}
    [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : rankOne Q split i ≃* SL(2,F)) {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n)
    (hcard : Nat.card (simpleRemainder Q split i) = Nat.card F ^ 2) :
    IsElementaryAbelian 2 (simpleRemainder Q split i) :=
  minimal_linear_two_group_elementary μ
    (split.isTwo.to_le (show simpleRemainder Q split i ≤ split.U from inf_le_left))
    (remainderRankOneAction Q split i hV)
    (remainder_action_moves_root Q split hm i j hij hV) hn hF hcard

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
