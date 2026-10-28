module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.Symplectic.FundamentalPlane.ThreeRank
public import Theory.SpecificGroups.Symplectic.FundamentalPlane.Centralizer

/-!
# The fundamental symplectic plane and residual rank in A.2.17

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), A.2.17, printed p.39.

Write the symplectic rank as `k+1`, with `k>0`. The marked nondegenerate
plane gives a proper, injective SL₂(F) in the literal `ClassicalGroup.PSp`.
The orthogonal complement gives an injective Sp₂ₖ(F), commuting with SL₂.
In odd characteristic the centralizer calculation identifies the entire
centralizer with this complement. Transvection generation then identifies
the actual residual `O^{r′}(C(K))` with the same full Sp₂ₖ(F). The equivalence
retains the literal complementary embedding after both subgroup inclusions.
Diagonal shears give rank at least `k*e`, while independent cubic rotations
give 3-rank at least `k`. Hence the source rank bound on J forces ambient
dimension four and field exponent one.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure
open Matrix
open Theory.SpecificGroups.Symplectic.FundamentalPlane

variable (F : Type*) [Field F] (k : ℕ)

/-- SL₂ on the first nondegenerate hyperbolic plane in the actual central quotient. -/
def symplecticFundamental : SpecialLinearGroup (Fin 2) F →* ClassicalGroup.PSp (k+1) F :=
  fundamental k

/-- The full symplectic group of the orthogonal complement. -/
def symplecticComplement : Matrix.symplecticGroup (Fin k) F →*
    ClassicalGroup.PSp (k+1) F := projectTail k

/-- The literal residual J in the source, inside the fundamental centralizer. -/
def symplecticResidual (r : ℕ) :=
  Subgroup.primeToResidual r
    (Subgroup.centralizer (symplecticFundamental F k).range.carrier)

theorem symplecticFundamental_injective (hk : 0 < k) :
    Function.Injective (symplecticFundamental F k) := fundamental_injective k hk

theorem symplecticFundamental_proper (hk : 0 < k) :
    (symplecticFundamental F k).range ≠ ⊤ := fundamental_proper k hk

theorem symplecticComplement_injective :
    Function.Injective (symplecticComplement F k) := projectTail_injective k

/-- The complementary factor retains its full center under the ambient quotient. -/
def symplecticComplementEquiv : Matrix.symplecticGroup (Fin k) F ≃*
    (symplecticComplement F k).range :=
  MonoidHom.ofInjective (symplecticComplement_injective F k)

theorem symplectic_factors_commute (a : SpecialLinearGroup (Fin 2) F)
    (b : Matrix.symplecticGroup (Fin k) F) :
    Commute (symplecticFundamental F k a) (symplecticComplement F k b) :=
  project_factors_commute k
    (Theory.SpecificGroups.SymplecticRoot.rankOneEquivSL.symm a) b

/-- Generation by r-elements gives an actual embedding into the literal J. -/
def symplecticComplementToResidual (r : ℕ) [CharP F r] :
    Matrix.symplecticGroup (Fin k) F →* symplecticResidual F k r :=
  tailToResidual k r

theorem symplecticComplementToResidual_injective (r : ℕ) [CharP F r] :
    Function.Injective (symplecticComplementToResidual F k r) :=
  tailToResidual_injective k r

/-- This is the same complementary matrix map after both subgroup inclusions. -/
theorem symplecticComplementToResidual_apply (r : ℕ) [CharP F r]
    (g : Matrix.symplecticGroup (Fin k) F) :
    (symplecticComplementToResidual F k r g).val.val = symplecticComplement F k g := rfl

/-- In odd characteristic every element of the literal J comes from the complement. -/
theorem symplecticComplementToResidual_surjective (r : ℕ)
    [Fact r.Prime] [CharP F r] (hr : r ≠ 2) :
    Function.Surjective (symplecticComplementToResidual F k r) :=
  tailToResidual_surjective k r hr

/-- The source identification `J ≅ Sp₂ₖ(F)`, induced by the complementary embedding. -/
def symplecticResidualEquiv (r : ℕ) [Fact r.Prime] [CharP F r] (hr : r ≠ 2) :
    Matrix.symplecticGroup (Fin k) F ≃* symplecticResidual F k r :=
  tailResidualEquiv k r hr

@[simp] theorem symplecticResidualEquiv_apply (r : ℕ)
    [Fact r.Prime] [CharP F r] (hr : r ≠ 2)
    (g : Matrix.symplecticGroup (Fin k) F) :
    symplecticResidualEquiv F k r hr g = symplecticComplementToResidual F k r g := rfl

/-- The identification uses the original quotient map, with no change of ambient group. -/
@[simp] theorem symplecticResidualEquiv_ambient (r : ℕ)
    [Fact r.Prime] [CharP F r] (hr : r ≠ 2)
    (g : Matrix.symplecticGroup (Fin k) F) :
    (symplecticResidualEquiv F k r hr g).val.val = symplecticComplement F k g := rfl

/-- The residual and complement are equal as subgroups of the actual PSp. -/
theorem symplecticResidual_map_eq_complement (r : ℕ)
    [Fact r.Prime] [CharP F r] (hr : r ≠ 2) :
    (symplecticResidual F k r).map
      (Subgroup.centralizer (symplecticFundamental F k).range.carrier).subtype =
      (symplecticComplement F k).range :=
  residual_map_eq_projectTail_range k r hr

theorem symplecticFundamental_involution (hk : 0 < k) {r : ℕ}
    [Fact r.Prime] [CharP F r] (hr : r ≠ 2) :
    let : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
    symplecticFundamental F k (-1) ≠ 1 ∧ symplecticFundamental F k (-1) ^ 2 = 1 :=
  fundamental_involution k hk hr

/-- Independent long-root groups give k copies of the additive defining field in J. -/
theorem symplectic_defining_rank [Finite F] {r d : ℕ} [Fact r.Prime] [CharP F r]
    (hcard : Nat.card F = r ^ d) :
    k * d ≤ primeRank r (symplecticResidual F k r) :=
  rank_mul_fieldExponent_le_residual k hcard

/-- One cubic rotation on each complementary hyperbolic plane gives the 3-rank witness. -/
theorem symplectic_three_rank [Finite F] (r : ℕ) [CharP F r] :
    k ≤ primeRank 3 (symplecticResidual F k r) :=
  ThreeRank.rank_le_primeRank_residual k r

/-- The symplectic structural branch of A.2.17, from the original field cardinality.
The explicit equivalence identifies the literal residual and its ambient embedding;
the two rank bounds discharge the source's numerical restriction on J. -/
theorem symplectic_structure [Finite F] (hk : 0 < k) {r d : ℕ}
    [Fact r.Prime] (hr : r ≠ 2) (hcard : Nat.card F = r ^ d) :
    Function.Injective (symplecticFundamental F k) ∧
      (symplecticFundamental F k).range ≠ ⊤ ∧
      ∃ j : Matrix.symplecticGroup (Fin k) F ≃* symplecticResidual F k r,
        (∀ g, (j g).val.val = symplecticComplement F k g) ∧
        k * d ≤ primeRank r (symplecticResidual F k r) ∧
        k ≤ primeRank 3 (symplecticResidual F k r) := by
  let := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact ⟨symplecticFundamental_injective F k hk, symplecticFundamental_proper F k hk,
    symplecticResidualEquiv F k r hr, symplecticResidualEquiv_ambient F k r hr,
    symplectic_defining_rank F k hcard, symplectic_three_rank F k r⟩

/-- The source's residual rank bound forces PSp₄(r), with the original field exponent. -/
theorem symplectic_dimension_of_residual_rank [Finite F] (hk : 0 < k) {r d : ℕ}
    [Fact r.Prime] (hcard : Nat.card F = r ^ d) (hd : 0 < d)
    (hJ : primeRank r (symplecticResidual F k r) ≤ 1) : k + 1 = 2 ∧ d = 1 := by
  let := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨hk1, hd1⟩ := dimension_of_residual_rank k hk hcard hd hJ
  exact ⟨by omega, hd1⟩

end CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure
