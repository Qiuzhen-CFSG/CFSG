module
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.MatrixResults
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import GorensteinWalter.PSL2Cardinality

/-!
# Exponent three and the binary-eight section obstruction in J₄

The certified order-27 word subgroup is Sylow in the actual matrix carrier.
Every nonidentity normal form is conjugate to one of two certified words
of order three. Sylow conjugacy therefore gives exponent three for every
three-subgroup of J₄. A surjection from a subgroup onto SL₂(8) would give
a cyclic Sylow three-subgroup of order nine and exponent three, a contradiction.

The point-component consumer applies this to the literal image of L in
I/Z(I), preserving its original two-core quotient. No new finite enumeration
or representation-theoretic assumption is needed.
Source: Aschbacher–Smith A.3.12(17) and 10.2.9, pp.47–48,750–751;
GLS3 Table 5.3i. The imported ATLAS program J4G1-max10W1 and matrix
certificates retain their attribution to Wilson, Nickerson and Bray.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Janko4
attribute [local irreducible] modelGroup matrixA matrixB
open Simplicity

private theorem threeLocal_representative_order (i : Fin 2) :
    orderOf (threeLocalRepresentative matrixA_mul_self matrixB_pow_four i) = 3 := by
  have hu := threeLocalU_fusion matrixA_mul_self matrixB_pow_four
  have hz := threeLocalZ_fusion matrixA_mul_self matrixB_pow_four
  have ho := orderOf_primeRepresentative_two matrixA_mul_self matrixB_pow_four
  fin_cases i
  · obtain ⟨g,hg⟩ := hu
    rw [hg] at ho
    exact ((MulAut.conj g).orderOf_eq _).symm.trans ho
  · obtain ⟨g,hg⟩ := hz
    rw [hg] at ho
    exact ((MulAut.conj g).orderOf_eq _).symm.trans ho

/-- The certified order-27 subgroup has exponent three. -/
theorem threeLocal_cube_eq_one (x : Model)
    (hx : x ∈ threeLocalSubgroup matrixA_mul_self matrixB_pow_four) : x ^ 3 = 1 := by
  obtain ⟨a,rfl⟩ := threeLocal_exhaustive matrixA_mul_self matrixB_pow_four x hx
  by_cases ha : a = (0,0,0)
  · rw [ha,threeLocalNormalForm_zero,one_pow]
  · obtain ⟨i,g,hg⟩ := threeLocalNormalForm_conjugacy matrixA_mul_self matrixB_pow_four a ha
    have ho := threeLocal_representative_order i
    rw [hg] at ho
    have he := ((MulAut.conj g).orderOf_eq _).symm.trans ho
    exact he ▸ pow_orderOf_eq_one _

/-- Every three-subgroup of the actual J₄ carrier has exponent dividing three. -/
theorem three_subgroup_cube_eq_one (P : Subgroup Model) (hp : IsPGroup 3 P)
    (x : P) : x ^ 3 = 1 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let U := threeLocalSubgroup matrixA_mul_self matrixB_pow_four
  have hU : IsPGroup 3 U := IsPGroup.of_card
    ((threeLocal_card matrixA_mul_self matrixB_pow_four).trans (by decide : 27 = 3 ^ 3))
  let S : Sylow 3 Model := hU.toSylow (three_not_dvd_index U Cardinality.model_card
    (threeLocal_card matrixA_mul_self matrixB_pow_four))
  obtain ⟨R,hPR⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model R S
  have hxU : (MulAut.conj g) (x : Model) ∈ U := by
    have h := mem_map_of_mem (MulAut.conj g).toMonoidHom (hPR x.property)
    change (MulAut.conj g) (x : Model) ∈ (g • R : Sylow 3 Model) at h
    rw [hg] at h
    exact h
  apply Subtype.ext
  apply (MulAut.conj g).injective
  change (MulAut.conj g) ((x : Model) ^ 3) = (MulAut.conj g) 1
  simpa only [map_pow,map_one] using threeLocal_cube_eq_one _ hxU

/-- An original subgroup of J₄ cannot map onto SL₂(8). The cyclic Sylow
three-subgroup of the image would have order nine and exponent three. -/
theorem no_binary_eight_quotient (B : Subgroup Model)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 8)
    (f : B →* SL(2,F)) (hf : Function.Surjective f) : False := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 B := Classical.choice inferInstance
  let S := P.mapSurjective hf
  let : IsCyclic S := Matrix.SL2.odd_pGroup_isCyclic_of_injective S.isPGroup'
    (by decide : 3 ≠ 2) (S : Subgroup SL(2,F)).subtype
    (S : Subgroup SL(2,F)).subtype_injective
  have hP (x : P) : x ^ 3 = 1 := by
    let Q := (P : Subgroup B).map B.subtype
    have h := three_subgroup_cube_eq_one Q (P.isPGroup'.map B.subtype)
      ⟨((x : B) : Model),mem_map_of_mem B.subtype x.property⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Q.subtype h
  have hS (s : S) : s ^ 3 = 1 := by
    obtain ⟨x,hx,hxs⟩ := (show (s : SL(2,F)) ∈ (P : Subgroup B).map f from s.property)
    apply Subtype.ext
    change (s : SL(2,F)) ^ 3 = 1
    rw [←hxs,←map_pow]
    have h := congrArg (P : Subgroup B).subtype (hP ⟨x,hx⟩)
    change x ^ 3 = 1 at h
    rw [h,map_one]
  have hcard : Nat.card S ∣ 3 := by
    rw [←IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hS
  have h9 : 9 ∣ Nat.card SL(2,F) := by
    rw [GorensteinWalter.sl2_card_formula,hF]
    norm_num
  rw [←(S : Subgroup SL(2,F)).card_mul_index] at h9
  have hcop : Nat.Coprime 9 (S : Subgroup SL(2,F)).index := by
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr S.not_dvd_index |>.pow_left 2
  have h9S : 9 ∣ Nat.card S := hcop.dvd_of_dvd_mul_right h9
  exact (by decide : ¬ 9 ∣ 3) (h9S.trans hcard)
end Janko4
