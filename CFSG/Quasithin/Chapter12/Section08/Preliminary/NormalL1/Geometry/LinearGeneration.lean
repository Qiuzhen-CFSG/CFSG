module

public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Geometry
public import Theory.SpecificGroups.BinaryLinear.PointResidualGeneration

/-!
# Point-residual generation on the actual invariant flag

The cardinalities of the marked subgroups identify their binary dimensions,
and monotonicity gives the strict inclusion of the first space in every
intermediate flag space. The structural point-residual calculation therefore
supplies the literal `hlinear` premise of `normal_geometry_of_linear_generation`.
No residual-generation hypothesis is retained. The argument applies in all
finite dimensions greater than two, in particular the source dimensions 3–5.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 12.8.2 and Lemma 12.8.5(2), printed pp.849–850 (PDF pp.866–867).
The earlier-source setup and the final geometric assembly remain with the
consumer of `normal_geometry_of_linear_generation`.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.NormalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {V : Subgroup G} {n : ℕ} [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem card_space (A : Subgroup G) (hAV : A ≤ V) :
    Nat.card (space (V := V) A) = Nat.card A := by
  let e : space (V := V) A ≃ A :=
    { toFun v := ⟨v.val.toMul, v.property⟩
      invFun a := ⟨Additive.ofMul ⟨a.val, hAV a.property⟩, a.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact Nat.card_congr e

private theorem finrank_flag_space (F : InvariantFlag T V n) (i : ℕ) (hi : i ≤ n) :
    Module.finrank (ZMod 2) (space (V := V) (F.Vi i)) = i := by
  have h := card_space (F.Vi i) (F.le_seed i)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, F.card i hi] at h
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) h

private theorem finrank_flag_seed (F : InvariantFlag T V n) :
    Module.finrank (ZMod 2) (Additive V) = n := by
  have h : Nat.card (Additive V) = 2 ^ n := by
    change Nat.card V = 2 ^ n
    rw [← F.last]
    exact F.card n le_rfl
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) h

private theorem flag_space_lt (F : InvariantFlag T V n) (hn : 2 < n)
    (i : ℕ) (hi : 1 < i) (hin : i < n) :
    space (V := V) (F.Vi 1) < space (V := V) (F.Vi i) := by
  refine lt_of_le_of_ne (fun v hv => F.monotone hi.le hv) ?_
  intro he
  have h := congrArg (fun W : Submodule (ZMod 2) (Additive V) =>
    Module.finrank (ZMod 2) W) he
  rw [finrank_flag_space F 1 (by omega), finrank_flag_space F i hin.le] at h
  omega

/-- The actual flag supplies the linear generation required in 12.8.5(2).
This is the literal `hlinear` argument of `normal_geometry_of_linear_generation`;
its proof uses only the marked flag and the elementary abelian seed. -/
theorem flag_linear_generation (F : InvariantFlag T V n) (hn : 2 < n) :
    ∀ i, 1 < i → i < n → conjugateSpanBy
      ((pResidual 2 (BinaryLinear.parabolic (space (V := V) (F.Vi 1)))).map
        (BinaryLinear.parabolic (space (V := V) (F.Vi 1))).subtype)
      (BinaryLinear.parabolic (space (V := V) (F.Vi i))) = ⊤ := by
  intro i hi hin
  apply BinaryLinear.PointResidualGeneration.conjugateSpanBy_point_residual_eq_top
  · rw [finrank_flag_seed F]
    omega
  · exact finrank_flag_space F 1 (by omega)
  · exact flag_space_lt F hn i hi hin

end CFSG.Quasithin.Chapter12.Section08.NormalGeometry
