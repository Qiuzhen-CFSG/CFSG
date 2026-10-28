module

public import Theory.AtlasPort.LinearGroups.G2.Torus
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.LinearCombination
public import Theory.AtlasPort.Algebra.SplitOctonion.NormGeometry
public import Mathlib.Algebra.CharP.Two

/-!
# Coordinates of a G₂ torus centralizer with a nonconstant fixed weight

In characteristic two, a unit `s ≠ 1` has three distinct weights
`1, s, s⁻¹` on the split octonions. Commutation with `torus 1 s` therefore
preserves the two planes on coordinates `(1,5)` and `(2,6)`. Preservation
of the norm pairing makes their matrices `A` and `det(A)⁻¹ A`.
Products between the planes span the four remaining coordinates and force
the complete action `blockApply`.

Thus every element of the actual centralizer has this formula with
`A = positiveBlock g` invertible, and restriction to the first plane is
faithful. Conversely, any actual automorphism realizing the formula
centralizes every `torus 1 s`. This file does not yet construct such an
automorphism for every invertible matrix, nor assert connectedness.
The statements retain all nonidentity parameters, including order three.

Source: the semisimple-centralizer argument of Steinberg, 8.1/8.5 and
12.5, `refs/KGroup/GLS3/Chapter2St2.tex`; GLS III, Sections 2.1 and 2.8,
`refs/KGroup/GLS3/chapter2.tex`. The coordinate conventions and octonion
multiplication are those of the licensed ATLAS port, Wilson's integral
table (4.11); see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section

open Atlas.SplitOctonion
open scoped CharTwo
set_option linter.unusedSectionVars false
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.FixedWeight
variable {K : Type*} [Field K] [CharP K 2]

private theorem coe_ne_inv (a : Kˣ) (ha : a ≠ 1) : (a : K) ≠ (↑a⁻¹ : K) := by
  intro h
  have hs : (a : K)^2 = 1 := by
    calc
      (a : K)^2 = (a : K) * (↑a⁻¹ : K) := by rw [pow_two, ← h]
      _ = 1 := by simp
  apply ha
  apply Units.ext
  have hz : ((a : K) + 1)^2 = 0 := by
    rw [add_sq, hs]
    simp
  exact (add_eq_zero_iff_eq_neg.mp ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hz)).trans (CharTwo.neg_eq 1)

private theorem commuting_weight (a : Kˣ) {g : Model K}
    (hg : g ∈ Subgroup.centralizer ({torus 1 a} : Set (Model K)))
    {x : Carrier K} {r : K} (hx : (torus 1 a).val x = r • x) (i : Fin 8) :
    ((torusWeights 1 a i : K) - r) * g.val x i = 0 := by
  have he := congrArg (fun z : Model K => z.val x)
    (Subgroup.mem_centralizer_singleton_iff.mp hg)
  change g.val ((torus 1 a).val x) = (torus 1 a).val (g.val x) at he
  rw [hx, map_smul] at he
  have hi := congrFun he i
  change r * g.val x i = (torusWeights 1 a i : K) * g.val x i at hi
  rw [sub_mul, ← hi, sub_self]

private theorem plus_shape (a : Kˣ) (ha : a ≠ 1) {g : Model K}
    (hg : g ∈ Subgroup.centralizer ({torus 1 a} : Set (Model K)))
    {x : Carrier K} (hx : (torus 1 a).val x = (a : K) • x) :
    g.val x = ![0, g.val x 1, 0, 0, 0, g.val x 5, 0, 0] := by
  have h1 : (1 : K) ≠ (a : K) := fun h => ha (Units.ext h.symm)
  have hi : (↑a⁻¹ : K) ≠ (a : K) := (coe_ne_inv a ha).symm
  have hz (i : Fin 8) (h : (torusWeights 1 a i : K) ≠ (a : K)) : g.val x i = 0 :=
    (mul_eq_zero.mp (commuting_weight a hg hx i)).resolve_left (sub_ne_zero.mpr h)
  have h0 := hz 0 (by simpa [torusWeights] using h1)
  have h2 := hz 2 (by simpa [torusWeights] using hi)
  have h3 := hz 3 (by simpa [torusWeights] using h1)
  have h4 := hz 4 (by simpa [torusWeights] using h1)
  have h6 := hz 6 (by simpa [torusWeights] using hi)
  have h7 := hz 7 (by simpa [torusWeights] using h1)
  ext i
  fin_cases i <;> simp [h0, h2, h3, h4, h6, h7]

private theorem minus_shape (a : Kˣ) (ha : a ≠ 1) {g : Model K}
    (hg : g ∈ Subgroup.centralizer ({torus 1 a} : Set (Model K)))
    {x : Carrier K} (hx : (torus 1 a).val x = (↑a⁻¹ : K) • x) :
    g.val x = ![0, 0, g.val x 2, 0, 0, 0, g.val x 6, 0] := by
  have h1 : (1 : K) ≠ (↑a⁻¹ : K) := by
    intro h
    apply ha
    exact inv_eq_one.mp (Units.ext h.symm)
  have hi : (a : K) ≠ (↑a⁻¹ : K) := coe_ne_inv a ha
  have hz (i : Fin 8) (h : (torusWeights 1 a i : K) ≠ (↑a⁻¹ : K)) : g.val x i = 0 :=
    (mul_eq_zero.mp (commuting_weight a hg hx i)).resolve_left (sub_ne_zero.mpr h)
  have h0 := hz 0 (by simpa [torusWeights] using h1)
  have h1' := hz 1 (by simpa [torusWeights] using hi)
  have h3 := hz 3 (by simpa [torusWeights] using h1)
  have h4 := hz 4 (by simpa [torusWeights] using h1)
  have h5 := hz 5 (by simpa [torusWeights] using hi)
  have h7 := hz 7 (by simpa [torusWeights] using h1)
  ext i
  fin_cases i <;> simp [h0, h1', h3, h4, h5, h7]

private theorem plus_basis_shape (a : Kˣ) (ha : a ≠ 1) {g : Model K}
    (hg : g ∈ Subgroup.centralizer ({torus 1 a} : Set (Model K)))
    (j : Fin 8) (hj : j = 1 ∨ j = 5) :
    g.val (basisVector j) =
      ![0, g.val (basisVector j) 1, 0, 0, 0, g.val (basisVector j) 5, 0, 0] := by
  apply plus_shape a ha hg
  rcases hj with rfl | rfl <;>
    (ext i; fin_cases i <;> simp [torus, torusEquiv, torusLinear, torusWeights, basisVector])

private theorem minus_basis_shape (a : Kˣ) (ha : a ≠ 1) {g : Model K}
    (hg : g ∈ Subgroup.centralizer ({torus 1 a} : Set (Model K)))
    (j : Fin 8) (hj : j = 2 ∨ j = 6) :
    g.val (basisVector j) =
      ![0, 0, g.val (basisVector j) 2, 0, 0, 0, g.val (basisVector j) 6, 0] := by
  apply minus_shape a ha hg
  rcases hj with rfl | rfl <;>
    (ext i; fin_cases i <;> simp [torus, torusEquiv, torusLinear, torusWeights, basisVector])

private theorem inverse_blocks (a b c d e f h i : K)
    (h11 : a*f+c*e=0) (h12 : a*i+c*h=1)
    (h21 : b*f+d*e=1) (h22 : b*i+d*h=0) :
    a*d+b*c ≠ 0 ∧
      e=(a*d+b*c)⁻¹*a ∧ f=(a*d+b*c)⁻¹*c ∧
      h=(a*d+b*c)⁻¹*b ∧ i=(a*d+b*c)⁻¹*d := by
  have hinv : (a*d+b*c)*(e*i+f*h)=1 := by
    linear_combination (norm := (ring_nf; simp)) (a*i+c*h)*h21 + h12 + (b*i+d*h)*h11
  have hd : a*d+b*c ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hinv
    exact zero_ne_one hinv
  refine ⟨hd, ?_, ?_, ?_, ?_⟩
  · apply (eq_inv_mul_iff_mul_eq₀ hd).mpr
    linear_combination (norm := (ring_nf; simp)) a*h21 + b*h11
  · apply (eq_inv_mul_iff_mul_eq₀ hd).mpr
    linear_combination (norm := (ring_nf; simp)) c*h21 + d*h11
  · apply (eq_inv_mul_iff_mul_eq₀ hd).mpr
    linear_combination (norm := (ring_nf; simp)) a*h22 + b*h12
  · apply (eq_inv_mul_iff_mul_eq₀ hd).mpr
    linear_combination (norm := (ring_nf; simp)) c*h22 + d*h12

/-- The linear action forced by a two-by-two block and its inverse determinant. -/
def blockApply (a b c d t : K) (x : Carrier K) : Carrier K :=
  ![t*(a^2*x 0+a*b*(x 3+x 4)+b^2*x 7),
    a*x 1+b*x 5,
    t*(a*x 2+b*x 6),
    t*(a*c*x 0+a*d*x 3+b*c*x 4+b*d*x 7),
    t*(a*c*x 0+b*c*x 3+a*d*x 4+b*d*x 7),
    c*x 1+d*x 5,
    t*(c*x 2+d*x 6),
    t*(c^2*x 0+c*d*(x 3+x 4)+d^2*x 7)]

def blockLinear (a b c d t : K) : Carrier K →ₗ[K] Carrier K where
  toFun := blockApply a b c d t
  map_add' x y := by ext i; fin_cases i <;> simp [blockApply] <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp [blockApply] <;> ring

/-- Restriction to the `s`-eigenspace, in the ordered basis `(e₁,e₅)`. -/
def positiveBlock (g : Model K) : Matrix (Fin 2) (Fin 2) K :=
  ![![g.val (basisVector 1) 1, g.val (basisVector 5) 1],
    ![g.val (basisVector 1) 5, g.val (basisVector 5) 5]]

private theorem block_basis_0 (a b c d t : K) :
    blockLinear a b c d t (basisVector 0) = mul ![0,a,0,0,0,c,0,0] ![0,0,t*a,0,0,0,t*c,0] := by
  ext i; fin_cases i <;>
    simp [blockLinear, blockApply, basisVector, mul, CharTwo.neg_eq] <;> ring

private theorem block_basis_1 (a b c d t : K) :
    blockLinear a b c d t (basisVector 1) = ![0,a,0,0,0,c,0,0] := by
  ext i; fin_cases i <;>
    simp [blockLinear, blockApply, basisVector]

private theorem block_basis_2 (a b c d t : K) :
    blockLinear a b c d t (basisVector 2) = ![0,0,t*a,0,0,0,t*c,0] := by
  ext i; fin_cases i <;>
    simp [blockLinear, blockApply, basisVector]

private theorem block_basis_3 (a b c d t : K) :
    blockLinear a b c d t (basisVector 3) = mul ![0,b,0,0,0,d,0,0] ![0,0,t*a,0,0,0,t*c,0] := by
  ext i; fin_cases i <;>
    simp [blockLinear, blockApply, basisVector, mul, CharTwo.neg_eq] <;> ring

private theorem block_basis_4 (a b c d t : K) :
    blockLinear a b c d t (basisVector 4) = mul ![0,a,0,0,0,c,0,0] ![0,0,t*b,0,0,0,t*d,0] := by
  ext i; fin_cases i <;>
    simp [blockLinear, blockApply, basisVector, mul, CharTwo.neg_eq] <;> ring

private theorem block_basis_5 (a b c d t : K) :
    blockLinear a b c d t (basisVector 5) = ![0,b,0,0,0,d,0,0] := by
  ext i; fin_cases i <;>
    simp [blockLinear, blockApply, basisVector]

private theorem block_basis_6 (a b c d t : K) :
    blockLinear a b c d t (basisVector 6) = ![0,0,t*b,0,0,0,t*d,0] := by
  ext i; fin_cases i <;>
    simp [blockLinear, blockApply, basisVector]

private theorem block_basis_7 (a b c d t : K) :
    blockLinear a b c d t (basisVector 7) = mul ![0,b,0,0,0,d,0,0] ![0,0,t*b,0,0,0,t*d,0] := by
  ext i; fin_cases i <;>
    simp [blockLinear, blockApply, basisVector, mul, CharTwo.neg_eq] <;> ring

/-- All centralizer coordinates are forced by an invertible two-dimensional block. -/
theorem block_coordinates (s : Kˣ) (hs : s ≠ 1) {g : Model K}
    (hg : g ∈ Subgroup.centralizer ({torus 1 s} : Set (Model K))) :
    (positiveBlock g).det ≠ 0 ∧
      ∀ x, g.val x = blockApply (positiveBlock g 0 0) (positiveBlock g 0 1)
        (positiveBlock g 1 0) (positiveBlock g 1 1) (positiveBlock g).det⁻¹ x := by
  let a := g.val (basisVector 1) 1
  let b := g.val (basisVector 5) 1
  let c := g.val (basisVector 1) 5
  let d := g.val (basisVector 5) 5
  let e := g.val (basisVector 2) 2
  let f := g.val (basisVector 2) 6
  let h := g.val (basisVector 6) 2
  let i := g.val (basisVector 6) 6
  have h1 : g.val (basisVector 1) = ![0,a,0,0,0,c,0,0] :=
    plus_basis_shape s hs hg 1 (Or.inl rfl)
  have h5 : g.val (basisVector 5) = ![0,b,0,0,0,d,0,0] :=
    plus_basis_shape s hs hg 5 (Or.inr rfl)
  have h2 : g.val (basisVector 2) = ![0,0,e,0,0,0,f,0] :=
    minus_basis_shape s hs hg 2 (Or.inl rfl)
  have h6 : g.val (basisVector 6) = ![0,0,h,0,0,0,i,0] :=
    minus_basis_shape s hs hg 6 (Or.inr rfl)
  have h11 : a*f+c*e=0 := by
    have hp := automorphism_normPolar g (basisVector 1) (basisVector 2)
    rw [h1, h2] at hp
    simpa [normPolar, basisVector] using hp
  have h12 : a*i+c*h=1 := by
    have hp := automorphism_normPolar g (basisVector 1) (basisVector 6)
    rw [h1, h6] at hp
    simpa [normPolar, basisVector] using hp
  have h21 : b*f+d*e=1 := by
    have hp := automorphism_normPolar g (basisVector 5) (basisVector 2)
    rw [h5, h2] at hp
    simpa [normPolar, basisVector] using hp
  have h22 : b*i+d*h=0 := by
    have hp := automorphism_normPolar g (basisVector 5) (basisVector 6)
    rw [h5, h6] at hp
    simpa [normPolar, basisVector] using hp
  obtain ⟨hdet, he, hf, hh, hi⟩ := inverse_blocks a b c d e f h i h11 h12 h21 h22
  have hdet' : (positiveBlock g).det = a*d+b*c := by
    rw [Matrix.det_fin_two]
    simp [positiveBlock, CharTwo.sub_eq_add, a, b, c, d]
  refine ⟨by rwa [hdet'], ?_⟩
  have hmul (j k : Fin 8) := automorphism_mul g (basisVector j) (basisVector k)
  have h0 : g.val (basisVector 0) = mul (g.val (basisVector 1)) (g.val (basisVector 2)) := by
    have hb : mul (basisVector 1) (basisVector 2) = (basisVector 0 : Carrier K) := by
      ext n; fin_cases n <;> simp [mul, basisVector, CharTwo.neg_eq]
    rw [← hb]
    exact hmul 1 2
  have h3 : g.val (basisVector 3) = mul (g.val (basisVector 5)) (g.val (basisVector 2)) := by
    have hb : mul (basisVector 5) (basisVector 2) = (basisVector 3 : Carrier K) := by
      ext n; fin_cases n <;> simp [mul, basisVector, CharTwo.neg_eq]
    rw [← hb]
    exact hmul 5 2
  have h4 : g.val (basisVector 4) = mul (g.val (basisVector 1)) (g.val (basisVector 6)) := by
    have hb : mul (basisVector 1) (basisVector 6) = (basisVector 4 : Carrier K) := by
      ext n; fin_cases n <;> simp [mul, basisVector, CharTwo.neg_eq]
    rw [← hb]
    exact hmul 1 6
  have h7 : g.val (basisVector 7) = mul (g.val (basisVector 5)) (g.val (basisVector 6)) := by
    have hb : mul (basisVector 5) (basisVector 6) = (basisVector 7 : Carrier K) := by
      ext n; fin_cases n <;> simp [mul, basisVector, CharTwo.neg_eq]
    rw [← hb]
    exact hmul 5 6
  have heq : g.val.toLinearMap = blockLinear a b c d (a*d+b*c)⁻¹ := by
    apply (Pi.basisFun K (Fin 8)).ext
    intro j
    rw [Pi.basisFun_apply]
    change g.val (basisVector j) = blockLinear a b c d (a*d+b*c)⁻¹ (basisVector j)
    fin_cases j
    · change g.val (basisVector 0) = blockLinear a b c d (a*d+b*c)⁻¹ (basisVector 0)
      rw [block_basis_0]
      simpa only [he, hf] using h0.trans (congrArg₂ mul h1 h2)
    · change g.val (basisVector 1) = blockLinear a b c d (a*d+b*c)⁻¹ (basisVector 1)
      rw [block_basis_1]
      exact h1
    · change g.val (basisVector 2) = blockLinear a b c d (a*d+b*c)⁻¹ (basisVector 2)
      rw [block_basis_2]
      simpa only [he, hf] using h2
    · change g.val (basisVector 3) = blockLinear a b c d (a*d+b*c)⁻¹ (basisVector 3)
      rw [block_basis_3]
      simpa only [he, hf] using h3.trans (congrArg₂ mul h5 h2)
    · change g.val (basisVector 4) = blockLinear a b c d (a*d+b*c)⁻¹ (basisVector 4)
      rw [block_basis_4]
      simpa only [hh, hi] using h4.trans (congrArg₂ mul h1 h6)
    · change g.val (basisVector 5) = blockLinear a b c d (a*d+b*c)⁻¹ (basisVector 5)
      rw [block_basis_5]
      exact h5
    · change g.val (basisVector 6) = blockLinear a b c d (a*d+b*c)⁻¹ (basisVector 6)
      rw [block_basis_6]
      simpa only [hh, hi] using h6
    · change g.val (basisVector 7) = blockLinear a b c d (a*d+b*c)⁻¹ (basisVector 7)
      rw [block_basis_7]
      simpa only [hh, hi] using h7.trans (congrArg₂ mul h5 h6)
  intro x
  have hex := LinearMap.congr_fun heq x
  rw [hdet']
  exact hex

/-- The two-dimensional block determines an actual centralizing automorphism. -/
theorem positiveBlock_injective (s : Kˣ) (hs : s ≠ 1) {g h : Model K}
    (hg : g ∈ Subgroup.centralizer ({torus 1 s} : Set (Model K)))
    (hh : h ∈ Subgroup.centralizer ({torus 1 s} : Set (Model K)))
    (he : positiveBlock g = positiveBlock h) : g = h := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [(block_coordinates s hs hg).2, (block_coordinates s hs hh).2, he]

/-- The displayed coordinate map commutes with every normalized torus element. -/
theorem blockApply_commute (s : Kˣ) (a b c d t : K) (x : Carrier K) :
    blockApply a b c d t ((torus 1 s).val x) =
      (torus 1 s).val (blockApply a b c d t x) := by
  ext i; fin_cases i <;>
    simp [blockApply, torus, torusEquiv, torusLinear, torusWeights] <;> ring

/-- Realizing the block formula as an automorphism automatically gives centralizer membership. -/
theorem mem_centralizer_of_blockApply (s : Kˣ) {g : Model K} {a b c d t : K}
    (hg : ∀ x, g.val x = blockApply a b c d t x) :
    g ∈ Subgroup.centralizer ({torus 1 s} : Set (Model K)) := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val ((torus 1 s).val x) = (torus 1 s).val (g.val x)
  rw [hg, hg]
  exact blockApply_commute s a b c d t x

end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.FixedWeight
