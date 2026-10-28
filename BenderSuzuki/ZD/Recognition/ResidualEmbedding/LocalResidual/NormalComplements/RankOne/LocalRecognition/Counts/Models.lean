module

public import Theory.GroupTheory.Involution.Counting
public import Theory.SpecificGroups.Suzuki.RootOmega
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import BenderSuzuki.Converse.PSL2
public import BenderSuzuki.SE.Borel

/-!
# Involution counts in the three concrete Bender Borels

A Borel is a Sylow two-normalizer, so its involutions are those of a
Sylow two-subgroup. For PSL₂ this is the additive root group; for Suzuki
the square-one elements are its root-group center; for PSU₃ the square
formula sets the first root coordinate to zero and leaves precisely the
fixed field. Removing the identity gives the required count in each case.

The Suzuki source exponent is `2 * m + 1`. The unitary branch retains
both the matrix-field order and the fixed-field order, and every model
transport uses an actual group isomorphism.

Source: GLS, Volume 4, Chapter 4, Lemma 3.2(b), used in Chapter 2,
Corollary 7.14.
-/

noncomputable section
open Theory.GroupTheory BenderSuzuki.PFAppendixIII Subgroup
namespace BenderSuzuki
open _root_.BenderSuzuki.MatrixGroups

/-- A binary PSL₂ Borel has one involution for each nonzero root parameter. -/
public theorem psl2_borel_involution_card {n : ℕ} (hn : 2 ≤ n)
    {B : Subgroup (PSL2BinaryMatrixGroup n)} (hB : IsBorelSubgroup B) :
    Nat.card {x : B // IsInvolution x} = 2 ^ n - 1 := by
  let K := BinaryGaloisField n
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow K 2
  let P : Sylow 2 (PSL2BinaryMatrixGroup n) :=
    U.mapSurjective (f := Converse.pi K) Converse.pi_surjective
  obtain ⟨_, S, rfl⟩ := hB
  refine (involution_card_normalizer S P).trans ?_
  let e0 : Multiplicative K ≃* Matrix.SpecialLinearGroup.upperUnipotent K :=
    MonoidHom.ofInjective (Matrix.SpecialLinearGroup.upperUnipotentHom_injective K)
  let e : Multiplicative K ≃* P := e0.trans
    ((U : Subgroup _).equivMapOfInjective (Converse.pi K) Converse.pi_injective)
  refine (involution_card_congr e).symm.trans ?_
  have hsq : ∀ x : Multiplicative K, x ^ 2 = 1 := by
    intro x
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    exact CharTwo.add_self_eq_zero x.toAdd
  refine (involution_card_eq_of_exponent_two hsq).trans ?_
  rw [Nat.card_congr Multiplicative.toAdd]
  congr 1
  exact GaloisField.card 2 n (by omega)

/-- The Suzuki root-center parameter gives the Borel involution count. -/
public theorem suzuki_borel_involution_card {m : ℕ} (hm : 1 ≤ m)
    {B : Subgroup (SuzukiMatrixGroup m)} (hB : IsBorelSubgroup B) :
    Nat.card {x : B // IsInvolution x} = 2 ^ (2 * m + 1) - 1 := by
  obtain ⟨_, S, rfl⟩ := hB
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  refine (involution_card_normalizer S P).trans ?_
  change Nat.card {x : (P : Subgroup (SuzukiMatrixGroup m)) // IsInvolution x} = _
  rw [hP]
  refine involution_card_eq_square_card_sub_one.trans ?_
  have he : Nat.card {x : SuzukiRootSubgroup m // x ^ 2 = 1} =
      Nat.card (center (SuzukiRootSubgroup m)) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) (suzukiRootSubgroup_square_iff_center m hm)
  rw [he, suzukiRootSubgroup_center_card m hm]

namespace UnitaryInvolutionCount
open BenderSuzuki.External
open HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage

/-- Square-one Hermitian root coordinates are parametrized by the fixed field. -/
public theorem coord_square_card {E : Type*} [Field E] [CharP E 2]
    (J : HermitianForm 3 E) :
    Nat.card {z : hermitianUnipotentCoord J // z ^ 2 = 1} =
      Nat.card {b : E // J.conj b = b} := by
  let f : {b : E // J.conj b = b} → {z : hermitianUnipotentCoord J // z ^ 2 = 1} := fun b =>
    ⟨⟨(0, b.val), by simp [b.property, CharTwo.add_self_eq_zero]⟩, by
      apply Subtype.ext
      rw [HermitianForm.EvenInner.square_coordinates]
      simp only [zero_mul]
      rfl⟩
  apply (Nat.card_congr (Equiv.ofBijective f ?_)).symm
  constructor
  · intro b c he
    exact Subtype.ext (congrArg (fun z => z.val.val.2) he)
  · intro z
    have hs := congrArg (fun w : hermitianUnipotentCoord J => w.val.2) z.property
    rw [HermitianForm.EvenInner.square_coordinates] at hs
    have hm : z.val.val.1 * J.conj z.val.val.1 = 0 := hs
    have hz : z.val.val.1 = 0 :=
      (mul_eq_zero.mp hm).elim id ((map_eq_zero J.conj).mp)
    have hb : J.conj z.val.val.2 = z.val.val.2 := by
      have hh := z.val.property
      rw [hz, zero_mul, add_zero] at hh
      exact (eq_neg_of_add_eq_zero_right hh).trans (CharTwo.neg_eq _)
    refine ⟨⟨z.val.val.2, hb⟩, ?_⟩
    exact Subtype.ext (Subtype.ext (Prod.ext hz.symm rfl))

private instance {E : Type*} [Field E] [Finite E] :
    Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- A binary PSU₃ Borel has fixed-field order minus one involutions. -/
public theorem psu3_borel_involution_card {n : ℕ} (hn : 2 ≤ n)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {b : E // J.conj b = b} = 2 ^ n)
    {B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)} (hB : IsBorelSubgroup B) :
    Nat.card {x : B // IsInvolution x} = 2 ^ n - 1 := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  obtain ⟨_, S, rfl⟩ := hB
  let P := HermitianForm.EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed
  refine (involution_card_normalizer S P).trans ?_
  let e : hermitianUnipotentCoord J ≃* P :=
    MulEquiv.ofBijective (root J hJ).rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr (root_injective J hJ),
        (root J hJ).rangeRestrict_surjective⟩
  refine (involution_card_congr e).symm.trans ?_
  refine involution_card_eq_square_card_sub_one.trans ?_
  rw [coord_square_card, hfixed]

end UnitaryInvolutionCount

/-- The actual model at source exponent `n` determines its Borel involution count. -/
public theorem bender_borel_involution_card_atExponent
    {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 2 ≤ n)
    (hmodel : IsSimpleBenderGroupAtExponent n G) {B : Subgroup G}
    (hB : IsBorelSubgroup B) : Nat.card {x : B // IsInvolution x} = 2 ^ n - 1 := by
  cases hmodel with
  | isPSL2 he =>
    obtain ⟨e⟩ := he
    rw [involution_card_congr (B.equivMapOfInjective e.toMonoidHom e.injective)]
    exact psl2_borel_involution_card hn (hB.map_mulEquiv e)
  | isSuzuki he =>
    obtain ⟨m, rfl, ⟨e⟩⟩ := he
    rw [involution_card_congr (B.equivMapOfInjective e.toMonoidHom e.injective)]
    exact suzuki_borel_involution_card (by omega) (hB.map_mulEquiv e)
  | isPSU3 he =>
    obtain ⟨E, hE, hfin, J, hJ, hcard, hfixed, ⟨e⟩⟩ := he
    let : Field E := hE
    let : Finite E := hfin
    rw [involution_card_congr (B.equivMapOfInjective e.toMonoidHom e.injective)]
    exact UnitaryInvolutionCount.psu3_borel_involution_card hn J hJ hcard hfixed
      (hB.map_mulEquiv e)

/-- Every simple Bender model has a Borel involution count of `2^n - 1`, with `n ≥ 2`. -/
public theorem bender_borel_involution_card {G : Type*} [Group G] [Finite G]
    (hmodel : IsSimpleBenderGroup G) {B : Subgroup G} (hB : IsBorelSubgroup B) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card {x : B // IsInvolution x} = 2 ^ n - 1 := by
  obtain ⟨n, hn, hmodel⟩ := hmodel.exists_exponent
  exact ⟨n, hn, bender_borel_involution_card_atExponent hn hmodel hB⟩
end BenderSuzuki
