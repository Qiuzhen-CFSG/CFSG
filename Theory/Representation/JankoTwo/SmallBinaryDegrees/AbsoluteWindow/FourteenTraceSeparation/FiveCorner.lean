module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveLocal
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Certificate
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Transport of the literal order-25 Hall--Janko corner

Every order-25 subgroup of the concrete degree-100 carrier is Sylow, by
its certified order 604800. Sylow conjugacy therefore gives an ambient
automorphism taking one such subgroup to any other. The induced group-algebra
isomorphism sends the literal norm sum to the other norm sum, and restricts
to a unital isomorphism between their actual idempotent corners.

`exclusion_of_one` applies this transport to the finite-algebra obstruction
needed for the degree-fourteen entry in Guralnick--Malle, Proposition 5.1,
p.16, and corrected Hiss--Malle Table 2. The exclusion for one subgroup remains
an explicit premise: this module does not assert `FiveCornerExclusion`.
The candidate presentation and its two independent proof contracts are
published in the imported `Certificate` module. `exclusion_of_certificate`
assembles those two inputs, including transport of the polynomial identities
through the actual corner homomorphism; both inputs remain unproved here.
-/

public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner
open Sporadic.LeechRelated.J2

/-- Restrict an actual ambient ring equivalence to the indicated corners. -/
def cornerEquiv {R S : Type*} [Ring R] [Ring S] {e : R} {d : S}
    (F : R ≃+* S) (he : IsIdempotentElem e) (hd : IsIdempotentElem d)
    (h : F e = d) : he.Corner ≃+* hd.Corner where
  toFun x := ⟨F x.val, by
    obtain ⟨r, hr⟩ := x.property
    refine ⟨F r, ?_⟩
    change d * F r * d = F x.val
    simpa only [map_mul, h] using congrArg F hr⟩
  invFun y := ⟨F.symm y.val, by
    obtain ⟨s, hs⟩ := y.property
    refine ⟨F.symm s, ?_⟩
    apply F.injective
    simpa only [map_mul, h, F.apply_symm_apply] using hs⟩
  left_inv x := Subtype.ext (F.symm_apply_apply x.val)
  right_inv y := Subtype.ext (F.apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (F.map_mul x.val y.val)
  map_add' x y := Subtype.ext (F.map_add x.val y.val)

set_option maxRecDepth 2000 in
/-- The group-algebra map sends the literal subgroup sum to its image sum. -/
theorem map_fiveNorm (F : Carrier ≃* Carrier) (P : Subgroup Carrier) :
    MonoidAlgebra.mapDomainRingEquiv (ZMod 2) F (fiveNorm P) =
      fiveNorm (P.map F.toMonoidHom) := by
  classical
  let := Fintype.ofFinite P
  let := Fintype.ofFinite (P.map F.toMonoidHom)
  rw [fiveNorm, fiveNorm, map_sum]
  simp only [MonoidAlgebra.mapDomainRingEquiv_single]
  let e : P ≃ P.map F.toMonoidHom := (F.subgroupMap P).toEquiv
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- The certified order of the literal carrier makes every order-25 subgroup Sylow. -/
theorem exists_map_eq (P Q : Subgroup Carrier) (hP : Nat.card P = 25)
    (hQ : Nat.card Q = 25) : ∃ F : Carrier ≃* Carrier, P.map F.toMonoidHom = Q := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have index_of_card (H : Subgroup Carrier) (hH : Nat.card H = 25) :
      ¬ 5 ∣ H.index := by
    have hi := H.card_mul_index
    rw [hH, ExceptionalParabolics.FirstParabolic.card_carrier] at hi
    have : H.index = 24192 := by omega
    rw [this]
    decide
  let SP : Sylow 5 Carrier :=
    (IsPGroup.of_card (p := 5) (n := 2) hP).toSylow (index_of_card P hP)
  let SQ : Sylow 5 Carrier :=
    (IsPGroup.of_card (p := 5) (n := 2) hQ).toSylow (index_of_card Q hQ)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier SP SQ
  refine ⟨MulAut.conj g, ?_⟩
  exact congrArg Sylow.toSubgroup hg

/-- A single literal order-25 corner calculation suffices for the universal contract.
The finite-algebra calculation for that subgroup remains an explicit premise. -/
theorem exclusion_of_one (P : Subgroup Carrier) (hP : Nat.card P = 25)
    (hexclude : ∀ (he : IsIdempotentElem (fiveNorm P))
      (f : he.Corner →+* Matrix (Fin 2) (Fin 2) (ZMod 2)), ¬ Function.Surjective f) :
    FiveCornerExclusion := by
  intro Q hQ heQ f hf
  obtain ⟨F, hF⟩ := exists_map_eq P Q hP hQ
  let A := MonoidAlgebra.mapDomainRingEquiv (ZMod 2) F
  have hn : A (fiveNorm P) = fiveNorm Q := by
    dsimp [A]
    rw [map_fiveNorm, hF]
  have heP : IsIdempotentElem (fiveNorm P) := by
    apply A.injective
    rw [map_mul, hn]
    exact heQ
  let E := cornerEquiv A heP heQ hn
  exact hexclude heP (f.comp E.toRingHom) (hf.comp E.surjective)

open Certificate

private theorem map_wordValue {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (x y : R) (n : ℕ) :
    f (wordValue x y n) = wordValue (f x) (f y) n := by
  simp only [wordValue, map_list_prod, List.map_map, Function.comp_def, apply_ite]

private theorem map_relationValue {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (r : Relation) (x : Fin 9 → R) :
    f (r.value x) = r.value (fun i => f (x i)) := by
  simp only [Relation.value, map_list_sum, List.map_map, Function.comp_def, map_wordValue]

open scoped IsMulCommutative in
/-- Assemble the two independently checked certificate inputs on the literal corner. -/
theorem exclusion_of_certificate (hp : LiteralPresentation) (hm : MatrixCommutativity) :
    FiveCornerExclusion := by
  obtain ⟨P, hP, hp⟩ := hp
  apply exclusion_of_one P hP
  intro he f hf
  obtain ⟨x, hx, hr⟩ := hp he
  have hs : Satisfies (fun i => f (x i)) := by
    intro r hmem
    rw [← map_relationValue, hr r hmem, map_zero]
  have hc := Subring.isMulCommutative_closure (s := Set.range (fun i => f (x i)))
    (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hm _ hs i j)
  have him : f '' Set.range x = Set.range (fun i => f (x i)) := by
    ext z
    simp
  have hcl : Subring.closure (Set.range (fun i => f (x i))) = f.range := by
    rw [← him, ← f.map_closure, hx]
    ext z
    simp
  rw [hcl, f.range_eq_top_of_surjective hf] at hc
  let := hc
  let A : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 0, 0]
  let B : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 0; 1, 0]
  have heq := mul_comm (⟨A, by trivial⟩ : (⊤ : Subring (Matrix (Fin 2) (Fin 2) (ZMod 2))))
    ⟨B, by trivial⟩
  have heq' : A * B = B * A := congrArg Subtype.val heq
  have hne : A * B ≠ B * A := by decide +kernel
  exact hne heq'

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner
