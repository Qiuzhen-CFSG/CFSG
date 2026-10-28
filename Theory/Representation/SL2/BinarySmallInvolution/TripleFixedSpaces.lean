module

public import Theory.Representation.SL2.BinarySmallInvolution.TripleFixedSpaces.Regular
public import Theory.Representation.PermutationBasisOrbits
public import Theory.Representation.InvariantsBaseChange
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# Fixed spaces exclude the binary SL₂(8) triple module

The triple tensor restricts to the regular module on the upper-unipotent
Sylow subgroup. Conjugating its orbit basis and counting subgroup orbits
gives fixed dimension times subgroup order equal to eight for every
two-subgroup. Invariants commute with scalar extension, so an actual
intertwining equivalence descends this identity to the binary module.
The nontrivial elementary subgroup orders 2, 4, and 8 give fixed dimensions
4, 2, and 1 and codimensions 4, 6, and 7. Each codimension exceeds twice
the subgroup's binary rank, excluding cubic ratio at most two.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the Steinberg
observation and K.3.1, printed pp.453–454. This calculation supplies the
exceptional-module exclusion; it does not assert the separate degree selection.
-/

@[expose] public section

open Module
namespace Representation.SL2.BinarySmall.TripleFixedSpaces
noncomputable section

/-- A basis permuted freely by a finite group gives fixed dimension equal to subgroup index. -/
private theorem regularBasis_fixed_mul_card {F P G V : Type*} [Field F] [Group P] [Finite P]
    [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (f : P →* G) (hf : Function.Injective f)
    (b : Basis P F V) (hb : ∀ g i, ρ (f g) (b i) = b (g * i))
    (A : Subgroup G) (hA : A ≤ f.range) :
    finrank F (Representation.invariants (ρ.comp A.subtype)) * Nat.card A = Nat.card P := by
  let B := A.comap f
  have hmap : B.map f = A := Subgroup.map_comap_eq_self hA
  have hfixed : (Representation.invariants ((ρ.comp f).comp B.subtype)) = (Representation.invariants (ρ.comp A.subtype)) := by
    ext v
    constructor
    · intro hv a
      obtain ⟨p, he⟩ := hA a.property
      have hpa : p ∈ B := by change f p ∈ A; rw [he]; exact a.property
      have hh : ρ (f p) v = v := hv ⟨p, hpa⟩
      change ρ a v = v
      rwa [he] at hh
    · intro hv b
      exact hv ⟨f b, b.property⟩
  have hd := Representation.permutedBasis_fixedSubspace_finrank_eq_orbitQuotient_card
    ((ρ.comp f).comp B.subtype) b (fun g i => hb g i)
  rw [hfixed] at hd
  have hc : Nat.card (MulAction.orbitRel.Quotient B P) = B.index :=
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel B)
  rw [hd, hc, ← hmap, Subgroup.card_map_of_injective hf]
  exact B.index_mul_card

/-- Conjugation preserves the regular basis property, with its literal embedding. -/
private theorem regularBasis_conjugate {F P G V : Type*} [Field F] [Group P] [Group G]
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) (f : P →* G)
    (b : Basis P F V) (hb : ∀ g i, ρ (f g) (b i) = b (g * i)) (c : G) :
    ∃ b' : Basis P F V,
      ∀ g i, ρ (((MulAut.conj c).toMonoidHom.comp f) g) (b' i) = b' (g * i) := by
  let e : V ≃ₗ[F] V :=
    { toLinearMap := ρ c
      invFun := ρ c⁻¹
      left_inv := ρ.inv_self_apply c
      right_inv := ρ.self_inv_apply c }
  refine ⟨b.map e, ?_⟩
  intro g i
  change ρ (c * f g * c⁻¹) (ρ c (b i)) = ρ c (b (g * i))
  simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply, hb]

/-- Intertwining equivalences identify fixed subspaces. -/
private def invariantsEquiv {F G V W : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W} (φ : ρ.Equiv σ) :
    ρ.invariants ≃ₗ[F] σ.invariants where
  toFun v := ⟨φ v, by
    intro g
    have h := IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g v
    rw [v.property g] at h
    exact h.symm⟩
  invFun v := ⟨φ.symm v, by
    intro g
    have h := IntertwiningMap.isIntertwining σ ρ φ.symm.toIntertwiningMap g v
    rw [v.property g] at h
    exact h.symm⟩
  left_inv v := Subtype.ext (φ.toLinearEquiv.symm_apply_apply v)
  right_inv v := Subtype.ext (φ.toLinearEquiv.apply_symm_apply v)
  map_add' x y := Subtype.ext (map_add φ (x : V) (y : V))
  map_smul' a v := Subtype.ext (map_smul φ a (v : V))

end
end Representation.SL2.BinarySmall.TripleFixedSpaces

open Module Matrix.SpecialLinearGroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2.BinarySmall.TripleFixedSpaces
noncomputable section
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- Every two-subgroup has the fixed dimension of a restriction of the regular Sylow module. -/
theorem triple_fixed_mul_card (hK : Nat.card K = 8)
    (A : Subgroup SL(2,K)) (hA : IsPGroup 2 A) :
    finrank K (Representation.invariants (k := K) (V := TripleSpace K) ((triple (K := K)).comp A.subtype)) * Nat.card A = 8 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨P, hAP⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2,K) (upperUnipotentSylow K 2) P
  let f := (MulAut.conj g).toMonoidHom.comp (upperUnipotentHom K)
  have hrange : f.range = P.toSubgroup := by
    rw [MonoidHom.range_comp]
    change (upperUnipotent K).map (MulAut.conj g).toMonoidHom = P.toSubgroup
    rw [← hg]
    rfl
  obtain ⟨b, hb⟩ := regularBasis_conjugate (F := K) (V := TripleSpace K) (triple (K := K)) (upperUnipotentHom K)
    (upperOrbitBasis hK) (upperOrbitBasis_equivariant hK) g
  have hd := regularBasis_fixed_mul_card (F := K) (V := TripleSpace K) (triple (K := K)) f
    ((MulAut.conj g).injective.comp (upperUnipotentHom_injective K)) b hb A
    (by rw [hrange]; exact hAP)
  rwa [Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K), hK] at hd

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
local instance : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- The binary form of the triple tensor has dimension eight. -/
theorem binary_finrank (σ : Representation (ZMod 2) SL(2,K) V) (hσ : IsTriple σ) :
    finrank (ZMod 2) V = 8 := by
  obtain ⟨e⟩ := hσ
  rw [← Module.finrank_baseChange (R := K) (S := ZMod 2), e.toLinearEquiv.finrank_eq]
  exact finrank_triple

/-- Fixed dimensions descend through the actual intertwining scalar extension. -/
theorem binary_fixed_mul_card (hK : Nat.card K = 8)
    (σ : Representation (ZMod 2) SL(2,K) V) (hσ : IsTriple σ)
    (A : Subgroup SL(2,K)) (hA : IsPGroup 2 A) :
    finrank (ZMod 2) (fixedSpace σ A) * Nat.card A = 8 := by
  obtain ⟨e⟩ := hσ
  let eA : Representation.Equiv ((extendScalars K σ).comp A.subtype)
      ((triple (K := K)).comp A.subtype) :=
    .mk e.toLinearEquiv (fun g => e.isIntertwining' g.val)
  have hbase := finrank_invariants_extendScalars_eq_of_finite (E := K) (σ.comp A.subtype)
  change finrank K (Representation.invariants ((extendScalars K σ).comp A.subtype)) =
    finrank (ZMod 2) (fixedSpace σ A) at hbase
  rw [← hbase, (invariantsEquiv (F := K) (W := TripleSpace K) eA).finrank_eq]
  exact triple_fixed_mul_card hK A hA

/-- The three nontrivial elementary two-subgroup orders give fixed dimensions 4, 2, and 1. -/
theorem binary_fixed_dimensions (hK : Nat.card K = 8)
    (σ : Representation (ZMod 2) SL(2,K) V) (hσ : IsTriple σ)
    (A : Subgroup SL(2,K)) (hA : IsElementaryTwo A) :
    (Nat.card A = 2 ∧ finrank (ZMod 2) (fixedSpace σ A) = 4 ∧ fixedCodim σ A = 4) ∨
    (Nat.card A = 4 ∧ finrank (ZMod 2) (fixedSpace σ A) = 2 ∧ fixedCodim σ A = 6) ∨
    (Nat.card A = 8 ∧ finrank (ZMod 2) (fixedSpace σ A) = 1 ∧ fixedCodim σ A = 7) := by
  let : IsElementaryAbelian 2 A := hA.2
  have hd := binary_fixed_mul_card hK σ hσ A (IsElementaryAbelian.isPGroup 2 A)
  have hc := fixedCodim_add_finrank σ A
  rw [binary_finrank σ hσ] at hc
  have ha := hA.card_eq_two_pow_rank
  have hrpos := hA.rank_pos
  have hrle : rank A ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [← ha]
    exact Nat.le_of_dvd (by decide : 0 < 8) ⟨_, hd.symm.trans (Nat.mul_comm _ _)⟩
  rw [ha] at hd
  interval_cases hr : rank A <;> norm_num [hr] at hrpos ha hd ⊢ <;> omega

/-- The exceptional triple tensor admits no cubic offender of ratio at most two. -/
theorem not_cubicRatio_le_two (hK : Nat.card K = 8)
    (σ : Representation (ZMod 2) SL(2,K) V) (hσ : IsTriple σ) :
    ¬ cubicRatio σ ≤ 2 := by
  intro hsmall
  obtain ⟨A, hA, _, hcodim⟩ := (cubicRatio_le_nat_iff σ 2).mp hsmall
  rcases binary_fixed_dimensions hK σ hσ A hA with h | h | h
  all_goals
    have hr : rank A = Nat.log 2 (Nat.card A) := rfl
    rw [h.1] at hr
    norm_num at hr
    omega

end
end Representation.SL2.BinarySmall.TripleFixedSpaces
