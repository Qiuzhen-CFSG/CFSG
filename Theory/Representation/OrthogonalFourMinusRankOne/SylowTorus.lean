module
public import Theory.Representation.OrthogonalFourMinusRankOne.RootActors
public import Theory.Representation.OrthogonalFourMinusRankOne.CartanFixed
public import Theory.SpecificGroups.SL2.OddBorelMarking
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Minus-torus fixation in the Hermitian rank-one module

Conjugate the specified Sylow subgroup and its odd normalizer subgroup to
upper unipotent and diagonal matrices. The Sylow-fixed space is the upper
singular line, where a diagonal element acts by its quadratic field norm.
Thus an odd normalizer fixes a nonzero vector exactly when its order divides
2ˢ+1. In particular a cubic fixer forces odd half-degree, and every element
annihilated by 2ˢ+1 fixes the whole Sylow-fixed space.

These calculations supply the orthogonal-module step in the last paragraph
of Aschbacher--Smith 5.1.13, printed p.638, refs/quasithin.pdf. The source
application keeps the literal two-core quotient and original Sylow choice.
-/

public noncomputable section
open Subgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Representation.OrthogonalFourMinus.SylowTorus
open FiniteModel RankOne CartanFixed BinaryOffender
variable (s : ℕ) [NeZero s]
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

private theorem rootVector_injective : Function.Injective (rootVector s) := by
  intro a b he
  exact Subtype.ext (congrArg (fun X : Space s => X.val 0 0) he)

private theorem fixed_rootVector (X : Space s)
    (hX : X ∈ fixedSpace (SL2.BinarySmall.hermitian s) (upperUnipotent (Field s))) :
    ∃ b : fixedField s, X = rootVector s b := by
  obtain ⟨hb,hz⟩ := (mem_fixedSpace_upper_iff s X).mp hX
  refine ⟨⟨X.val 0 0,entry_fixed s X 0⟩,?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · simpa [rootVector,coordinates_symm_val] using hz
  · simpa [rootVector,coordinates_symm_val,hz] using (entry_conjugate s X 1 0).symm
  · simpa [rootVector,coordinates_symm_val] using hb

private theorem diagonal_fixed_iff (a : (Field s)ˣ) (X : Space s)
    (hX : X ∈ fixedSpace (SL2.BinarySmall.hermitian s) (upperUnipotent (Field s)))
    (hne : X ≠ 0) :
    action s (CartanFixed.diagonal s a) X = X ↔ a^(2^s+1)=1 := by
  obtain ⟨b,rfl⟩ := fixed_rootVector s X hX
  have hb : b ≠ 0 := by
    intro he
    apply hne
    rw [he]
    exact (coordinates s).symm.map_zero
  rw [diagonal_rootVector, (rootVector_injective s).eq_iff]
  have he : FiniteModel.norm s a * b = b ↔ FiniteModel.norm s a = 1 := by
    constructor
    · intro h
      exact mul_right_cancel₀ hb (h.trans (one_mul b).symm)
    · intro h; rw [h,one_mul]
  rw [he]
  constructor
  · intro h
    apply Units.ext
    have hh := congrArg Subtype.val h
    change (a : Field s) * conjugation s a = 1 at hh
    simpa only [conjugation,iterateFrobeniusEquiv_def,Units.val_pow_eq_pow_val,Units.val_one,Units.val_mul,pow_succ,mul_comm] using hh
  · intro h
    apply Subtype.ext
    have hh := congrArg Units.val h
    change (a : Field s) * conjugation s a = 1
    simpa only [conjugation,iterateFrobeniusEquiv_def,Units.val_pow_eq_pow_val,Units.val_one,Units.val_mul,pow_succ,mul_comm] using hh

omit [NeZero s] in
private theorem diagonal_power (a : (Field s)ˣ) (k : ℕ) :
    (CartanFixed.diagonal s a)^k=1 ↔ a^k=1 := by
  let f := (rankOneBorel (Field s)).subtype.comp (borelDiagonalHom (F := Field s))
  have hf : Function.Injective f := by
    intro a b h
    apply Units.ext
    have he := congrArg (fun g : SL(2,Field s) => g.val 0 0) h
    change (diag2 (a : Field s) a.ne_zero).val 0 0 =
      (diag2 (b : Field s) b.ne_zero).val 0 0 at he
    simpa [diag2_coe'] using he
  change (f a)^k=1 ↔ a^k=1
  rw [←map_pow]
  exact hf.eq_iff' (map_one f)

private theorem conj_fixed (ρ : Representation (ZMod 2) SL(2,Field s) (Space s))
    (a g : SL(2,Field s)) (X : Space s) :
    ρ (a*g*a⁻¹) (ρ a X) = ρ a X ↔ ρ g X = X := by
  have hi : Function.Injective (ρ a) := (ρ.apply_bijective a).injective
  have he : ρ (a*g*a⁻¹) (ρ a X) = ρ a (ρ g X) := by
    rw [←Module.End.mul_apply,←map_mul]
    simp only [mul_assoc,inv_mul_cancel,mul_one,map_mul,Module.End.mul_apply]
  rw [he]
  exact hi.eq_iff

/-- On a nonzero Sylow-fixed Hermitian vector, an odd normalizer acts
trivially precisely when its order divides the norm-one exponent. -/
theorem odd_normalizer_fixed_iff
    (S : Sylow 2 SL(2,Field s)) (g : SL(2,Field s))
    (hg : g ∈ normalizer (S : Set SL(2,Field s))) (ho : Odd (orderOf g))
    (X : Space s) (hX : X ∈ fixedSpace (SL2.BinarySmall.hermitian s) S)
    (hne : X ≠ 0) :
    SL2.BinarySmall.hermitian s g X = X ↔ g^(2^s+1)=1 := by
  let C := zpowers g
  have hC : C ≤ normalizer (S : Set SL(2,Field s)) := zpowers_le.mpr hg
  have hCo : Odd (Nat.card C) := by simpa only [C,Nat.card_zpowers] using ho
  obtain ⟨a,d,hS,hd⟩ := sylow_odd_subgroup_diagonal_coordinates S C hC hCo
  let ρ := SL2.BinarySmall.hermitian s
  let Y := ρ a X
  have hY : Y ∈ fixedSpace ρ (upperUnipotent (Field s)) := by
    rw [←hS]
    intro b
    obtain ⟨b₀,hb₀,he⟩ := b.property
    change ρ (b : SL(2,Field s)) (ρ a X) = ρ a X
    rw [←he]
    exact (conj_fixed s ρ a b₀ X).mpr (hX ⟨b₀,hb₀⟩)
  have hYne : Y ≠ 0 := fun he => hne ((ρ.apply_bijective a).injective (he.trans (map_zero _).symm))
  let gC : C := ⟨g,mem_zpowers g⟩
  have hgdiag : a*g*a⁻¹ = CartanFixed.diagonal s (d gC) := hd gC
  have hfix := conj_fixed s ρ a g X
  rw [hgdiag] at hfix
  have hpow : (CartanFixed.diagonal s (d gC))^(2^s+1)=1 ↔ g^(2^s+1)=1 := by
    rw [←hgdiag,←MulAut.conj_apply,←map_pow]
    exact (MulAut.conj a).map_eq_one_iff
  exact hfix.symm.trans ((diagonal_fixed_iff s (d gC) Y hY hYne).trans
    ((diagonal_power s (d gC) _).symm.trans hpow))

/-- Every minus-torus root fixes the whole Sylow-fixed space. -/
theorem minus_root_fixes (S : Sylow 2 SL(2,Field s)) (g : SL(2,Field s))
    (hg : g ∈ normalizer (S : Set SL(2,Field s))) (hp : g^(2^s+1)=1)
    (X : Space s) (hX : X ∈ fixedSpace (SL2.BinarySmall.hermitian s) S) :
    SL2.BinarySmall.hermitian s g X = X := by
  by_cases hz : X = 0
  · rw [hz,map_zero]
  apply (odd_normalizer_fixed_iff s S g hg ?_ X hX hz).mpr hp
  have ho : Odd (2^s+1) := by
    have he : Even (2^s) := even_two.pow_of_ne_zero (NeZero.ne s)
    exact he.add_odd odd_one
  exact ho.of_dvd_nat (orderOf_dvd_of_pow_eq_one hp)

/-- A cubic fixing a nonzero Sylow-fixed vector forces odd half-degree. -/
theorem half_degree_odd_of_cubic_fixed (S : Sylow 2 SL(2,Field s))
    (g : SL(2,Field s)) (hg : g ∈ normalizer (S : Set SL(2,Field s)))
    (ho : orderOf g = 3) (X : Space s)
    (hX : X ∈ fixedSpace (SL2.BinarySmall.hermitian s) S) (hne : X ≠ 0)
    (hfix : SL2.BinarySmall.hermitian s g X = X) : Odd s := by
  have hp := (odd_normalizer_fixed_iff s S g hg (by rw [ho]; decide) X hX hne).mp hfix
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [ho] at hd
  have hm := Nat.BinaryTorusParity.two_pow_mod_three s
  have hz := Nat.mod_eq_zero_of_dvd hd
  apply Nat.odd_iff.mpr
  split_ifs at hm <;> omega

end Representation.OrthogonalFourMinus.SylowTorus
