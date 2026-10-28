module

public import Theory.SpecificGroups.PSL3Three.FiniteModel
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.FinCases

/-!
# Orders of the four concrete candidates in PSL₃(3)

The full setwise line and plane stabilizers each have order 432, the monomial
subgroup has order 24, and the specified Singer normalizer has order 39.
The canonical injective projection transfers the counts from SL₃(3).

For the parabolics, seven coordinates describe every matrix, and the determinant
condition leaves 432 choices. For the monomial subgroup, the columns are the
six signed coordinate vectors; exactly 24 triples have determinant one.
For the Singer normalizer, conjugation sends the generator to one of its
thirteen powers. The intertwining equation determines the matrix from that
power and its first column. Exactly 39 of the resulting 351 parameters satisfy
the determinant and intertwining conditions, and the parametrization is
bijective. All finite counts are checked by kernel reduction.

These compute the actual subgroups from `Subgroups`, including the full
setwise parabolics. They supply the numerical premises used in `Order432Core`;
no subgroup classification or parabolic core calculation is assumed here.

Source: GLS III, Theorem 6.5.3(a–c), `refs/KGroup/GLS3/chapter6.tex`;
Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511 (PDF p.528).
-/

namespace Matrix.PSL3Three

private abbrev ParabolicParameters := {v : Fin 7 → ZMod 3 //
  v 0 * (v 3 * v 6 - v 4 * v 5) = 1}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem card_parabolicParameters : Fintype.card ParabolicParameters = 432 := by decide +kernel

private def lineMatrix (v : Fin 7 → ZMod 3) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![v 0, v 1, v 2; 0, v 3, v 4; 0, v 5, v 6]

private theorem lineMatrix_det (v : ParabolicParameters) : (lineMatrix v.val).det = 1 := by
  simpa [lineMatrix, det_fin_three, mul_sub, mul_assoc] using v.property

private def lineEquiv : ParabolicParameters ≃ lineStabilizerSL where
  toFun v := ⟨⟨lineMatrix v.val, lineMatrix_det v⟩,
    (mem_lineStabilizerSL_iff _).mpr ⟨rfl, rfl⟩⟩
  invFun g := ⟨![g.val.val 0 0, g.val.val 0 1, g.val.val 0 2,
    g.val.val 1 1, g.val.val 1 2, g.val.val 2 1, g.val.val 2 2], by
      obtain ⟨h1, h2⟩ := (mem_lineStabilizerSL_iff g.val).mp g.property
      have hd := g.val.property
      rw [det_fin_three] at hd
      simpa [det_fin_three, h1, h2, mul_sub, mul_assoc] using hd⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv g := by
    obtain ⟨h1, h2⟩ := (mem_lineStabilizerSL_iff g.val).mp g.property
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lineMatrix, h1, h2]

private def planeMatrix (v : Fin 7 → ZMod 3) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![v 0, 0, 0; v 1, v 3, v 4; v 2, v 5, v 6]

private theorem planeMatrix_det (v : ParabolicParameters) : (planeMatrix v.val).det = 1 := by
  simpa [planeMatrix, det_fin_three, mul_sub, mul_assoc] using v.property

private def planeEquiv : ParabolicParameters ≃ planeStabilizerSL where
  toFun v := ⟨⟨planeMatrix v.val, planeMatrix_det v⟩,
    (mem_planeStabilizerSL_iff _).mpr ⟨rfl, rfl⟩⟩
  invFun g := ⟨![g.val.val 0 0, g.val.val 1 0, g.val.val 2 0,
    g.val.val 1 1, g.val.val 1 2, g.val.val 2 1, g.val.val 2 2], by
      obtain ⟨h1, h2⟩ := (mem_planeStabilizerSL_iff g.val).mp g.property
      have hd := g.val.property
      rw [det_fin_three] at hd
      simpa [h1, h2, mul_sub, mul_assoc] using hd⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv g := by
    obtain ⟨h1, h2⟩ := (mem_planeStabilizerSL_iff g.val).mp g.property
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [planeMatrix, h1, h2]

private def signedVector : Fin 6 → Fin 3 → ZMod 3 :=
  ![![1, 0, 0], ![2, 0, 0], ![0, 1, 0], ![0, 2, 0], ![0, 0, 1], ![0, 0, 2]]

private theorem signedVector_injective : Function.Injective signedVector := by decide

private theorem signedVector_norm (i : Fin 6) :
    signedVector i 0 ^ 2 + signedVector i 1 ^ 2 + signedVector i 2 ^ 2 = 1 := by
  revert i; decide

private theorem signedVector_surjective : ∀ v : Fin 3 → ZMod 3,
    v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 → ∃ i, signedVector i = v := by decide

private def monoMatrix (v : Fin 3 → Fin 6) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  fun i j => signedVector (v j) i

private abbrev MonoParameters := {v : Fin 3 → Fin 6 // (monoMatrix v).det = 1}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem card_monoParameters : Fintype.card MonoParameters = 24 := by decide +kernel

private def monoMap (v : MonoParameters) : monomialSL :=
  ⟨⟨monoMatrix v.val, v.property⟩,
    (mem_monomialSL_iff_columns _).mpr (fun j => signedVector_norm (v.val j))⟩

private theorem monoMap_bijective : Function.Bijective monoMap := by
  constructor
  · intro v w he
    apply Subtype.ext
    funext j
    apply signedVector_injective
    funext i
    exact congrArg (fun g : monomialSL => g.val.val i j) he
  · intro g
    have hc := (mem_monomialSL_iff_columns g.val).mp g.property
    have he (j : Fin 3) : ∃ i, signedVector i = fun k => g.val.val k j :=
      signedVector_surjective _ (hc j)
    choose v hv using he
    have hm : monoMatrix v = g.val.val := by
      ext i j
      exact congrFun (hv j) i
    refine ⟨⟨v, hm ▸ g.val.property⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext hm

private theorem singerNormalizer_iff (g : SL) : g ∈ singerNormalizerSL ↔
    ∃ k : Fin 13, g * singerGenerator = singerGenerator ^ k.val * g := by
  constructor
  · intro hg
    have hc : g * singerGenerator * g⁻¹ ∈ singerSubgroupSL :=
      (Subgroup.mem_normalizer_iff.mp hg singerGenerator).mp (Subgroup.mem_zpowers _)
    rw [mem_singerSubgroupSL_iff, singerPowers, Finset.mem_image] at hc
    obtain ⟨k, hk, he⟩ := hc
    exact ⟨⟨k, Finset.mem_range.mp hk⟩, (mul_inv_eq_iff_eq_mul).mp he.symm⟩
  · rintro ⟨k, hk⟩
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    apply Subgroup.eq_of_le_of_card_ge
    · rw [singerSubgroupSL, MonoidHom.map_zpowers]
      apply Subgroup.zpowers_le.mpr
      change g * singerGenerator * g⁻¹ ∈ Subgroup.zpowers singerGenerator
      rw [hk, mul_inv_cancel_right]
      exact Subgroup.npow_mem_zpowers _ _
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private def singerMatrix (p : Fin 13 × (Fin 3 → ZMod 3)) :
    Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  let a := (singerGenerator ^ p.1.val).val
  fun i j => ![p.2, a.mulVec p.2, a.mulVec (a.mulVec p.2)] j i

private theorem singerMatrix_eq (m a : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (h : m * singerGenerator.val = a * m) :
    m = fun i j => ![fun k => m k 0, a.mulVec (fun k => m k 0),
      a.mulVec (a.mulVec (fun k => m k 0))] j i := by
  have h1 : (fun i => m i 1) = a.mulVec (fun i => m i 0) := by
    funext i
    have hi := congrArg (fun b : Matrix (Fin 3) (Fin 3) (ZMod 3) => b i 0) h
    simpa [mul_apply, mulVec, dotProduct, Fin.sum_univ_three, singerGenerator] using hi
  have h2 : (fun i => m i 2) = a.mulVec (fun i => m i 1) := by
    funext i
    have hi := congrArg (fun b : Matrix (Fin 3) (Fin 3) (ZMod 3) => b i 1) h
    simpa [mul_apply, mulVec, dotProduct, Fin.sum_univ_three, singerGenerator] using hi
  ext i j
  fin_cases j
  · rfl
  · exact congrFun h1 i
  · exact congrFun (h2.trans (congrArg a.mulVec h1)) i

private abbrev SingerParameters := {p : Fin 13 × (Fin 3 → ZMod 3) //
  (singerMatrix p).det = 1 ∧
    singerMatrix p * singerGenerator.val = (singerGenerator ^ p.1.val).val * singerMatrix p}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem card_singerParameters : Fintype.card SingerParameters = 39 := by decide +kernel

private def singerMap (p : SingerParameters) : singerNormalizerSL :=
  ⟨⟨singerMatrix p.val, p.property.1⟩, (singerNormalizer_iff _).mpr
    ⟨p.val.1, Subtype.ext p.property.2⟩⟩

private theorem singerMap_bijective : Function.Bijective singerMap := by
  constructor
  · intro p q he
    have hm : singerMatrix p.val = singerMatrix q.val :=
      congrArg (fun g : singerNormalizerSL => g.val.val) he
    have hk : p.val.1 = q.val.1 := by
      have hp' : (singerMap p).val * singerGenerator =
          singerGenerator ^ p.val.1.val * (singerMap p).val := Subtype.ext p.property.2
      have hq' : (singerMap q).val * singerGenerator =
          singerGenerator ^ q.val.1.val * (singerMap q).val := Subtype.ext q.property.2
      rw [he] at hp'
      have hpow := mul_right_cancel (hp'.symm.trans hq')
      apply Fin.ext
      exact pow_injOn_Iio_orderOf (by rw [orderOf_singerGenerator]; exact p.val.1.isLt)
        (by rw [orderOf_singerGenerator]; exact q.val.1.isLt) hpow
    have hv : p.val.2 = q.val.2 := by
      funext i
      exact congrArg (fun m : Matrix (Fin 3) (Fin 3) (ZMod 3) => m i 0) hm
    exact Subtype.ext (Prod.ext hk hv)
  · intro g
    obtain ⟨k, hk⟩ := (singerNormalizer_iff g.val).mp g.property
    have hm : singerMatrix (k, fun i => g.val.val i 0) = g.val.val :=
      (singerMatrix_eq g.val.val (singerGenerator ^ k.val).val
        (congrArg Subtype.val hk)).symm
    refine ⟨⟨(k, fun i => g.val.val i 0), ?_⟩, ?_⟩
    · constructor
      · rw [hm]; exact g.val.property
      · rw [hm]; exact congrArg Subtype.val hk
    · apply Subtype.ext
      exact Subtype.ext hm

/-- The full setwise stabilizer of the first coordinate line in SL₃(3)
has order 432. -/
public theorem card_lineStabilizerSL : Nat.card lineStabilizerSL = 432 := by
  rw [← Nat.card_congr lineEquiv, Nat.card_eq_fintype_card]
  exact card_parabolicParameters

/-- The full setwise stabilizer of the last two coordinate plane in SL₃(3)
has order 432. -/
public theorem card_planeStabilizerSL : Nat.card planeStabilizerSL = 432 := by
  rw [← Nat.card_congr planeEquiv, Nat.card_eq_fintype_card]
  exact card_parabolicParameters

/-- The determinant-one monomial subgroup of SL₃(3) has order 24. -/
public theorem card_monomialSL : Nat.card monomialSL = 24 := by
  rw [← Nat.card_congr (Equiv.ofBijective monoMap monoMap_bijective),
    Nat.card_eq_fintype_card]
  exact card_monoParameters

/-- The normalizer of the specified order-thirteen subgroup of SL₃(3)
has order 39. -/
public theorem card_singerNormalizerSL : Nat.card singerNormalizerSL = 39 := by
  rw [← Nat.card_congr (Equiv.ofBijective singerMap singerMap_bijective),
    Nat.card_eq_fintype_card]
  exact card_singerParameters

/-- The full setwise line stabilizer in PSL₃(3) has order 432. -/
public theorem card_lineStabilizer : Nat.card lineStabilizer = 432 := by
  rw [lineStabilizer, Subgroup.card_map_of_injective project_injective, card_lineStabilizerSL]

/-- The full setwise plane stabilizer in PSL₃(3) has order 432. -/
public theorem card_planeStabilizer : Nat.card planeStabilizer = 432 := by
  rw [planeStabilizer, Subgroup.card_map_of_injective project_injective, card_planeStabilizerSL]

/-- The monomial subgroup in PSL₃(3) has order 24. -/
public theorem card_monomial : Nat.card monomial = 24 := by
  rw [monomial, Subgroup.card_map_of_injective project_injective, card_monomialSL]

/-- The specified Singer normalizer in PSL₃(3) has order 39. -/
public theorem card_singerNormalizer : Nat.card singerNormalizer = 39 := by
  rw [singerNormalizer, Subgroup.card_map_of_injective project_injective, card_singerNormalizerSL]

end Matrix.PSL3Three
