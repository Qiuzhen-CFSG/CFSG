module
public import GorensteinWalter.PGammaL2Subgroups
public import Mathlib.GroupTheory.IndexNormal

/-!
# The concrete outer product quotient of PGammaL2

Over a finite field of odd order, the linear coset and coefficient coordinates
give a surjective homomorphism from PGammaL2 onto (PGL2/PSL2) × Aut(F).
Its kernel is exactly the canonical PSL2 range. The quotient normality
instance is fixed by the actual PSL2 index-two theorem and shared by the map
and its specifications.

Coefficient automorphisms preserve PSL2, hence act trivially on the quotient
of order two. This proves multiplicativity of the coordinate map. Its kernel
is read from the two coordinates, and quotient representatives give
surjectivity. The construction is extracted from the existing outer-abelian
proof so that the index-two subgroup arguments use the same concrete map.

This supplies the three outer involution lines used to define and identify
PGL* in Alperin--Brauer--Gorenstein II.2, article p20, and II.3 Proposition 4,
article p29. It does not assume a classification of those subgroups.
-/

namespace GorensteinWalter
universe u

public instance pgl2PSLRangeNormal (K : Type u) [Field K] [Finite K]
    [Fact (IsOddPrimePower (Nat.card K))] :
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.Normal :=
  Subgroup.normal_of_index_eq_two (pgl2_psl2Range_index_eq_two K Fact.out)

@[expose] public def pGammaL2OuterProduct (K : Type u) [Field K] [Finite K]
    [Fact (IsOddPrimePower (Nat.card K))] :
    PGammaL2 K →* (PGL2 K ⧸ (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range) × (K ≃+* K) := by
  let t : PSL2 K →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL
  let N := t.range
  let q := QuotientGroup.mk' N
  have hc : Nat.card (PGL2 K ⧸ N) = 2 :=
    pgl2_psl2Range_index_eq_two K Fact.out
  have hinv (σ : K ≃+* K) (g : PGL2 K) :
      pgl2FieldAut K σ g ∈ N ↔ g ∈ N := by
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨psl2FieldAut K σ⁻¹ x, ?_⟩
      rw [psl2FieldAut_toPGL, hx, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    · rintro ⟨x, rfl⟩
      exact ⟨psl2FieldAut K σ x, psl2FieldAut_toPGL σ x⟩
  have hclass (σ : K ≃+* K) (g : PGL2 K) : q (pgl2FieldAut K σ g) = q g := by
    have hone : q (pgl2FieldAut K σ g) = 1 ↔ q g = 1 := by
      simpa only [q, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] using hinv σ g
    obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : PGL2 K ⧸ N)).mp hc
    by_cases hg : q g = 1
    · exact (hone.mpr hg).trans hg.symm
    · exact (hz _ (fun h => hg (hone.mp h))).trans (hz _ hg).symm
  exact {
    toFun a := (q a.left, a.right)
    map_one' := by simp
    map_mul' a b := by
      apply Prod.ext
      · change q (a.left * pgl2FieldAut K a.right b.left) = q a.left * q b.left
        rw [map_mul, hclass]
      · rfl }

public theorem pGammaL2OuterProduct_apply (K : Type u) [Field K] [Finite K]
    [Fact (IsOddPrimePower (Nat.card K))] (a : PGammaL2 K) :
    pGammaL2OuterProduct K a = (QuotientGroup.mk a.left, a.right) := rfl

public theorem pGammaL2OuterProduct_ker (K : Type u) [Field K] [Finite K]
    [Fact (IsOddPrimePower (Nat.card K))] :
    (pGammaL2OuterProduct K).ker = pGammaL2PSLRange K := by
  ext a
  constructor
  · intro ha
    have hf := MonoidHom.mem_ker.mp ha
    have hleft : QuotientGroup.mk' _ a.left = 1 := congrArg Prod.fst hf
    have hright : a.right = 1 := congrArg Prod.snd hf
    obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff a.left).mp hleft
    refine ⟨x, ?_⟩
    apply SemidirectProduct.ext
    · exact hx
    · exact hright.symm
  · rintro ⟨x, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply Prod.ext
    · exact (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
    · rfl

public theorem pGammaL2OuterProduct_surjective (K : Type u) [Field K] [Finite K]
    [Fact (IsOddPrimePower (Nat.card K))] :
    Function.Surjective (pGammaL2OuterProduct K) := by
  rintro ⟨c, σ⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ c
  exact ⟨⟨g, σ⟩, rfl⟩

end GorensteinWalter

