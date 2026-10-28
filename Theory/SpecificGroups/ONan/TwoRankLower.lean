module
public import Theory.SpecificGroups.ONan.TwoRankLower.Matrices
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# A genuine elementary eight in the projective O’Nan carrier

The final three certified binary basis words are commuting involutions.
Their eight products have distinct scalar classes, detected by the first
two off-diagonal entries in the first row. Thus their actual projective
images give an elementary eight; no Sylow or model order is assumed.
Source: ATLAS ONG1-max9W1; Aschbacher–Smith A.2.12, printed p.36.
-/

namespace ONan.TwoRankLower
open Simplicity.TwoCertificate Simplicity.TwoCertificate.Enumeration
open Simplicity.TwoCertificate.Enumeration.WordValues
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev E := (C2 × C2) × C2

private def binaryHom {H : Type*} [Group H] (g : H) (hg : g ^ 2 = 1) : C2 →* H where
  toFun a := if a = 1 then 1 else g
  map_one' := by simp
  map_mul' a b := by
    have cases2 : ∀ x : C2, x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide +kernel
    have hsum : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := rfl
    have hone : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide +kernel
    rcases cases2 a with rfl | rfl <;> rcases cases2 b with rfl | rfl <;>
      simp [hsum, hone, ← pow_two, hg]

private theorem binary_commute {H : Type*} [Group H] {a b : H}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b) (x y : C2) :
    Commute (binaryHom a ha x) (binaryHom b hb y) := by
  change Commute (if x = 1 then 1 else a) (if y = 1 then 1 else b)
  split_ifs <;> simp [hab]

private def tripleHom {H : Type*} [Group H] (a b c : H)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) : E →* H :=
  ((binaryHom a ha).noncommCoprod (binaryHom b hb) (binary_commute ha hb hab)).noncommCoprod
    (binaryHom c hc) (fun x y =>
      (binary_commute ha hc hac x.1 y).mul_left (binary_commute hb hc hbc x.2 y))

private theorem sq_a : linearGenerators 6 ^ 2 = 1 := by
  rw [pow_two]
  apply Units.ext
  change (linearGenerators 6 : Mat) * (linearGenerators 6 : Mat) = 1
  rw [Matrices.linear_a, Matrices.a_sq]
private theorem sq_b : linearGenerators 7 ^ 2 = 1 := by
  rw [pow_two]
  apply Units.ext
  change (linearGenerators 7 : Mat) * (linearGenerators 7 : Mat) = 1
  rw [Matrices.linear_b, Matrices.b_sq]
private theorem sq_c : linearGenerators 8 ^ 2 = 1 := by
  rw [pow_two]
  apply Units.ext
  change (linearGenerators 8 : Mat) * (linearGenerators 8 : Mat) = 1
  rw [Matrices.linear_c, Matrices.c_sq]
private theorem comm_ab : Commute (linearGenerators 6) (linearGenerators 7) := by
  apply Units.ext
  change (linearGenerators 6 : Mat) * (linearGenerators 7 : Mat) =
    (linearGenerators 7 : Mat) * (linearGenerators 6 : Mat)
  rw [Matrices.linear_a, Matrices.linear_b, Matrices.mul_ab, Matrices.mul_ba]
private theorem comm_ac : Commute (linearGenerators 6) (linearGenerators 8) := by
  apply Units.ext
  change (linearGenerators 6 : Mat) * (linearGenerators 8 : Mat) =
    (linearGenerators 8 : Mat) * (linearGenerators 6 : Mat)
  rw [Matrices.linear_a, Matrices.linear_c, Matrices.mul_ac, Matrices.mul_ca]
private theorem comm_bc : Commute (linearGenerators 7) (linearGenerators 8) := by
  apply Units.ext
  change (linearGenerators 7 : Mat) * (linearGenerators 8 : Mat) =
    (linearGenerators 8 : Mat) * (linearGenerators 7 : Mat)
  rw [Matrices.linear_b, Matrices.linear_c, Matrices.mul_bc, Matrices.mul_cb]
private theorem generator_sq {i : Fin 9} (h : linearGenerators i ^ 2 = 1) : generators i ^ 2 = 1 := by
  apply Subtype.ext
  change (generators i).val ^ 2 = 1
  rw [← project_linearGenerators, ← map_pow, h, map_one]
private theorem generator_comm {i j : Fin 9}
    (h : Commute (linearGenerators i) (linearGenerators j)) : Commute (generators i) (generators j) := by
  apply Subtype.ext
  change (generators i).val * (generators j).val = (generators j).val * (generators i).val
  rw [← project_linearGenerators, ← project_linearGenerators, ← map_mul, ← map_mul, h.eq]
private def linearEmbedding : E →* Linear :=
  tripleHom (linearGenerators 6) (linearGenerators 7) (linearGenerators 8)
    sq_a sq_b sq_c comm_ab comm_ac comm_bc
private def embedding : E →* Model :=
  tripleHom (generators 6) (generators 7) (generators 8)
    (generator_sq sq_a) (generator_sq sq_b) (generator_sq sq_c)
    (generator_comm comm_ab) (generator_comm comm_ac) (generator_comm comm_bc)
private theorem projection (x : E) :
    Matrix.ProjGenLinGroup.mk (linearEmbedding x) = (embedding x).val := by
  simp only [linearEmbedding, embedding, tripleHom, MonoidHom.noncommCoprod_apply,
    binaryHom, MonoidHom.coe_mk, OneHom.coe_mk, map_mul]
  split_ifs <;> simp [project_linearGenerators] <;> rfl
private def rows (x : E) : Packed :=
  if x.1.1 = 1 then
    if x.1.2 = 1 then (if x.2 = 1 then Matrices.unit else Matrices.c)
    else (if x.2 = 1 then Matrices.b else Matrices.bc)
  else if x.1.2 = 1 then (if x.2 = 1 then Matrices.a else Matrices.ac)
    else (if x.2 = 1 then Matrices.ab else Matrices.abc)
private theorem matrixImage (x : E) : (linearEmbedding x : Mat) = decode (rows x) := by
  simp only [linearEmbedding, tripleHom, MonoidHom.noncommCoprod_apply,
    binaryHom, MonoidHom.coe_mk, OneHom.coe_mk, rows]
  split_ifs <;> simp [Matrices.linear_a,
    Matrices.linear_b, Matrices.linear_c, Matrices.decode_unit,
    Matrices.mul_ab, Matrices.mul_ac, Matrices.mul_bc, Matrices.mul_abc]
private theorem detected : ∀ x : E,
    decode (rows x) 0 1 = 0 → decode (rows x) 0 2 = 0 → x = 1 := by
  decide +kernel
private theorem embedding_injective : Function.Injective embedding := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hp : Matrix.ProjGenLinGroup.mk (linearEmbedding x) =
      Matrix.ProjGenLinGroup.mk (1 : Linear) := by
    rw [projection,hx,map_one]
    rfl
  obtain ⟨u,hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have he (j : Fin 45) : decode (rows x) 0 j * u.val = (1 : Mat) 0 j := by
    have h := congrArg (fun a : Linear => (a : Mat) 0 j) hu
    change (((linearEmbedding x : Mat) * Matrix.scalar (Fin 45) u.val) 0 j) =
      (1 : Mat) 0 j at h
    simpa only [Matrix.scalar_apply, Matrix.mul_diagonal, matrixImage] using h
  apply detected
  · exact u.mul_left_eq_zero.mp (by simpa using he 1)
  · exact u.mul_left_eq_zero.mp (by simpa using he 2)
/-- The literal projective O’Nan carrier contains an elementary abelian group of order eight. -/
public theorem three_le_twoRank : 3 ≤ primeRank 2 Model := by
  apply primeRank_ge_of_elementary_embedding (f := embedding)
  · exact (by decide +kernel : ∀ x : E, x ^ 2 = 1)
  · simp [E, C2, Nat.card_eq_fintype_card]
  · exact embedding_injective
end ONan.TwoRankLower
