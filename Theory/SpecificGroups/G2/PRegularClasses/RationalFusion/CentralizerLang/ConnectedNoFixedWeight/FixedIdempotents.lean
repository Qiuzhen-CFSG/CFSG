module

public import Theory.AtlasPort.LinearGroups.G2.Torus
public import Mathlib.Algebra.CharP.Two

/-!
# Fixed idempotents in the no-fixed-weight centralizer

The hypotheses `l ≠ 1`, `m ≠ 1`, `l ≠ m` cut the torus fixed space down to
coordinates 3 and 4. In characteristic two the weight of coordinate 0 is
also distinct from every weight outside coordinates 0, 5, 6. A commuting
automorphism therefore takes the nonzero vector at coordinate 0 into that
three-space. Multiplication by its image of the first idempotent, together
with trace preservation, forces the first idempotent to be fixed. Preservation
of the identity gives the second. No distinctness within a weight triple is
assumed.

This is a coordinate step toward the G₂ instance of Steinberg 8.5 and 12.5,
`refs/KGroup/GLS3/Chapter2St2.tex`. Products use the licensed ATLAS split-octonion
table (`Theory.AtlasPort.Algebra.SplitOctonion.Basic`, `LICENSES/ATLAS.txt`).
-/

public section

open Atlas.SplitOctonion
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
variable {K : Type*} [Field K]

private theorem torus_basis (l m : Kˣ) (j : Fin 8) :
    (torus l m).val (basisVector j) = (torusWeights l m j : K) • basisVector j := by
  ext i
  by_cases h : i = j
  · subst i
    simp [torus, torusEquiv, torusLinear, basisVector]
  · simp [torus, torusEquiv, torusLinear, basisVector, h]

/-- Commutation with the literal diagonal torus forces unequal-weight entries to vanish. -/
theorem centralizer_entry_zero (l m : Kˣ) (g : Model K)
    (hg : g ∈ Subgroup.centralizer ({torus l m} : Set (Model K)))
    (i j : Fin 8) (hij : torusWeights l m i ≠ torusWeights l m j) :
    g.val (basisVector j) i = 0 := by
  have h := congrArg (fun a : Model K => a.val (basisVector j))
    (Subgroup.mem_centralizer_singleton_iff.mp hg)
  change g.val ((torus l m).val (basisVector j)) =
    (torus l m).val (g.val (basisVector j)) at h
  rw [torus_basis, map_smul] at h
  have hi := congrFun h i
  change (torusWeights l m j : K) * g.val (basisVector j) i =
    (torusWeights l m i : K) * g.val (basisVector j) i at hi
  exact (mul_eq_mul_right_iff.mp hi).resolve_left (fun he => hij (Units.ext he.symm))

private theorem unit_ne_inv [CharP K 2] (l : Kˣ) (hl : l ≠ 1) : l ≠ l⁻¹ := by
  intro h
  have hs : (l : K) ^ 2 = 1 := by
    calc
      _ = (l : K) * (↑l⁻¹ : K) := by rw [pow_two, ← h]
      _ = 1 := Units.mul_inv l
  rcases sq_eq_one_iff.mp hs with he | he
  · exact hl (Units.ext he)
  · exact hl (Units.ext (he.trans (CharTwo.neg_eq 1)))

/-- Under the no-fixed-weight hypotheses, the fixed space is exactly the diagonal two-space. -/
theorem torus_fixed_iff (l m : Kˣ) (hl : l ≠ 1) (hm : m ≠ 1) (hlm : l ≠ m)
    (x : Carrier K) :
    (torus l m).val x = x ↔ ∀ i : Fin 8, i ≠ 3 → i ≠ 4 → x i = 0 := by
  have hweight (i : Fin 8) (hi3 : i ≠ 3) (hi4 : i ≠ 4) : torusWeights l m i ≠ 1 := by
    fin_cases i <;> simp_all [torusWeights, mul_inv_eq_one, inv_mul_eq_one, eq_comm]
  constructor
  · intro h i hi3 hi4
    have he := congrFun h i
    change (torusWeights l m i : K) * x i = x i at he
    exact (mul_eq_mul_right_iff.mp (he.trans (one_mul _).symm)).resolve_left (fun hh => hweight i hi3 hi4 (Units.ext hh))
  · intro h
    ext i
    by_cases hi3 : i = 3
    · subst i; simp [torus, torusEquiv, torusLinear, torusWeights]
    by_cases hi4 : i = 4
    · subst i; simp [torus, torusEquiv, torusLinear, torusWeights]
    change (torusWeights l m i : K) * x i = x i
    rw [h i hi3 hi4, mul_zero]

theorem centralizer_basis_zero_support [CharP K 2]
    (l m : Kˣ) (hl : l ≠ 1) (hm : m ≠ 1) (hlm : l ≠ m)
    (g : Model K) (hg : g ∈ Subgroup.centralizer ({torus l m} : Set (Model K)))
    (i : Fin 8) (hi0 : i ≠ 0) (hi5 : i ≠ 5) (hi6 : i ≠ 6) :
    g.val (basisVector 0) i = 0 := by
  apply centralizer_entry_zero l m g hg i 0
  have hinv := unit_ne_inv l hl
  fin_cases i <;> simp_all [torusWeights, eq_comm]

/-- The two fixed idempotents cannot be interchanged by a torus-centralizing automorphism. -/
theorem centralizer_fixes_idempotents [CharP K 2]
    (l m : Kˣ) (hl : l ≠ 1) (hm : m ≠ 1) (hlm : l ≠ m)
    (g : Model K) (hg : g ∈ Subgroup.centralizer ({torus l m} : Set (Model K))) :
    g.val (basisVector 3) = basisVector 3 ∧ g.val (basisVector 4) = basisVector 4 := by
  have hfixed : (torus l m).val (g.val (basisVector 3)) = g.val (basisVector 3) := by
    have h := congrArg (fun a : Model K => a.val (basisVector 3))
      (Subgroup.mem_centralizer_singleton_iff.mp hg)
    change g.val ((torus l m).val (basisVector 3)) =
      (torus l m).val (g.val (basisVector 3)) at h
    rw [torus_basis] at h
    simpa [torusWeights] using h.symm
  have hs := (torus_fixed_iff l m hl hm hlm _).mp hfixed
  have hz := centralizer_basis_zero_support l m hl hm hlm g hg
  have hprod : mul (g.val (basisVector 3)) (g.val (basisVector 0)) =
      g.val (basisVector 3) 3 • g.val (basisVector 0) := by
    ext i
    fin_cases i <;>
      simp [mul, hs 0 (by decide) (by decide), hs 1 (by decide) (by decide),
        hs 2 (by decide) (by decide), hs 5 (by decide) (by decide),
        hs 6 (by decide) (by decide), hs 7 (by decide) (by decide),
        hz 1 (by decide) (by decide) (by decide), hz 2 (by decide) (by decide) (by decide),
        hz 3 (by decide) (by decide) (by decide), hz 4 (by decide) (by decide) (by decide),
        hz 7 (by decide) (by decide) (by decide)]
  have h30 : mul (basisVector 3 : Carrier K) (basisVector 0) = basisVector 0 := by
    ext i; fin_cases i <;> simp [mul, basisVector]
  have hnonzero : g.val (basisVector 0) ≠ 0 := by
    intro he
    have hb : (basisVector 0 : Carrier K) = 0 := g.val.injective (he.trans (map_zero g.val).symm)
    have := congrFun hb 0
    simp [basisVector] at this
  have heq : g.val (basisVector 3) 3 • g.val (basisVector 0) =
      (1 : K) • g.val (basisVector 0) := by
    rw [← hprod, ← automorphism_mul, h30, one_smul]
  have h3 : g.val (basisVector 3) 3 = 1 := (smul_left_injective K hnonzero) heq
  have htrace := automorphism_trace g (basisVector 3)
  have h4 : g.val (basisVector 3) 4 = 0 := by
    rw [show trace (basisVector 3 : Carrier K) = 1 by simp [trace, basisVector]] at htrace
    change g.val (basisVector 3) 3 + g.val (basisVector 3) 4 = 1 at htrace
    rw [h3] at htrace
    simpa using htrace
  have he3 : g.val (basisVector 3) = basisVector 3 := by
    ext i
    fin_cases i <;> simp_all [basisVector]
  refine ⟨he3, ?_⟩
  have hu : (basisVector 3 : Carrier K) + basisVector 4 = unit := by
    ext i; fin_cases i <;> simp [basisVector, unit]
  have hsum := automorphism_unit g
  rw [← hu, map_add, he3] at hsum
  exact add_left_cancel hsum

end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
