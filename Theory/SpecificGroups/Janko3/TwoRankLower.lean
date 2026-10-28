module

public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.Certificates
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod
/-!
# Four independent involutions in the actual J₃ carrier

The four certified commuting translation involutions generate an elementary
sixteen. Independence is detected on point zero of the existing permutation
model; this uses only sixteen point evaluations, not a new group enumeration.
Source: GLS, Number 3, Table 5.3h, printed p.269; Aschbacher–Smith A.2.12,
printed p.36.
-/

namespace Sporadic.Janko3.TwoRank
open ThreeCoverConfig TwoLocal
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev E3 := (C2 × C2) × C2
private abbrev E := E3 × C2

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
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) : E3 →* H :=
  ((binaryHom a ha).noncommCoprod (binaryHom b hb) (binary_commute ha hb hab)).noncommCoprod
    (binaryHom c hc) (fun x y =>
      (binary_commute ha hc hac x.1 y).mul_left (binary_commute hb hc hbc x.2 y))


private abbrev a := elementaryGenerator 0
private abbrev b := elementaryGenerator 1
private abbrev c := elementaryGenerator 2
private abbrev d := elementaryGenerator 3
private def embedding : E →* Model :=
  (tripleHom a b c (elementary_square 0) (elementary_square 1) (elementary_square 2)
    (elementary_commute 0 1) (elementary_commute 0 2) (elementary_commute 1 2)).noncommCoprod
    (binaryHom d (elementary_square 3)) (fun x y =>
      ((binary_commute (elementary_square 0) (elementary_square 3)
        (elementary_commute 0 3) x.1.1 y).mul_left
        (binary_commute (elementary_square 1) (elementary_square 3)
          (elementary_commute 1 3) x.1.2 y)).mul_left
        (binary_commute (elementary_square 2) (elementary_square 3)
          (elementary_commute 2 3) x.2 y))
private theorem image (x : E) :
    (embedding x : Equiv.Perm (Fin 6156)) =
      (if x.1.1.1 = 1 then 1 else qPerm 0) *
      (if x.1.1.2 = 1 then 1 else qPerm 1) *
      (if x.1.2 = 1 then 1 else qPerm 2) *
      (if x.2 = 1 then 1 else qPerm 3) := by
  simp only [embedding, tripleHom, MonoidHom.noncommCoprod_apply, binaryHom,
    MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs <;> simp [a, b, c, d, qPerm_eq]
private theorem detected : ∀ x : E,
    ((if x.1.1.1 = 1 then 1 else qPerm 0) *
      (if x.1.1.2 = 1 then 1 else qPerm 1) *
      (if x.1.2 = 1 then 1 else qPerm 2) *
      (if x.2 = 1 then 1 else qPerm 3)) 0 = 0 → x = 1 := by
  decide +kernel
private theorem embedding_injective : Function.Injective embedding := by
  rw [injective_iff_map_eq_one]
  intro x hx
  apply detected
  have he := congrArg (fun g : Model => (g : Equiv.Perm (Fin 6156)) 0) hx
  simpa only [image, OneMemClass.coe_one, Equiv.Perm.one_apply] using he
/-- The literal J₃ carrier contains an elementary abelian subgroup of order sixteen. -/
public theorem four_le_twoRank : 4 ≤ primeRank 2 Model := by
  apply primeRank_ge_of_elementary_embedding (f := embedding)
  · exact (by decide +kernel : ∀ x : E, x ^ 2 = 1)
  · simp [E, E3, C2, Nat.card_eq_fintype_card]
  · exact embedding_injective
end Sporadic.Janko3.TwoRank
