module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.MatrixConditions
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence

/-!
# Order exclusion and cubic containment in the actual max2 quotient

A subgroup of order 6912 has a Sylow two-subgroup of order 256. Conjugating
that subgroup to the certified base subgroup allows the double-coset sieve to
place the whole subgroup in one of the two concrete candidates. Lagrange's
theorem then reduces exclusion to two explicit candidate-order obstructions.

If the ambient three-core has order three, adjoining it to an elementary
pair product either changes nothing or creates a subgroup of order 6912.
The exclusion therefore puts the core in the pair product. Its normality
then puts it in the elementary factor, which is Sylow three in that product.
This last step establishes containment in R itself.

The finite witness and candidate-order hypotheses below are explicit. These
reductions do not by themselves establish the unconditional matrix conditions.
Source context: Aschbacher--Smith, Proposition 1.3.4, printed p.511/PDF p.528
of refs/quasithin.pdf; GLS3 Table 5.3i.
-/

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2
open FiniteIncidence

/-- Once order 6912 is excluded, an order-three core lies in every elementary
order-nine factor that permutes with a Sylow two-subgroup. -/
public theorem elementaryCubicContainment_of_order27Exclusion
    (hC : Nat.card (pCore 3 MatrixGroup) = 3) (hexcl : Order27Exclusion) :
    ElementaryCubicContainment := by
  intro S R hE hR hp
  let C := pCore 3 MatrixGroup
  let K : Subgroup MatrixGroup := R ⊔ S.toSubgroup
  have hK : Nat.card K = 2304 := involutionMatrixPair_card S R hE hR hp
  have hCK : C ≤ K := by
    have hd : Nat.card (C ⊓ K : Subgroup MatrixGroup) ∣ 3 :=
      hC ▸ card_dvd_of_le (inf_le_left : C ⊓ K ≤ C)
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h1 | h3
    · have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes C K
        (show K ≤ normalizer (C : Set MatrixGroup) from le_normalizer_of_normal)
      rw [hC, hK, h1, one_mul] at hprod
      exact (hexcl (C ⊔ K) hprod.symm).elim
    · have heq : C ⊓ K = C := eq_of_le_of_card_ge inf_le_left (by rw [h3, hC])
      exact heq ▸ inf_le_right
  let T : Sylow 3 K := Sylow.ofCard (R.subgroupOf K) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show R ≤ K from le_sup_left)).toEquiv,
      hR, hK]
    decide +kernel)
  have hCT : C.subgroupOf K ≤ T.toSubgroup :=
    (pCore_isPGroup.comap_subtype : IsPGroup 3 (C.subgroupOf K)).le_sylow_of_normal T
  intro x hx
  exact hCT (show (⟨x, hCK hx⟩ : K) ∈ C.subgroupOf K from hx)


private theorem overgroup_le_candidate
    (hrep : ∀ j : Fin 110,
      representative j ∈ involutionMatrixLineStabilizer ∨
      representative j ∈ involutionMatrixSecondSubgroup ∨
      ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative j), x ^ 6912 ≠ 1)
    (K : Subgroup MatrixGroup) (hPK : baseSubgroup ≤ K) (hK : Nat.card K = 6912) :
    K ≤ involutionMatrixLineStabilizer ∨ K ≤ involutionMatrixSecondSubgroup := by
  apply SubgroupClass.subset_union.mp
  intro x hx
  obtain ⟨j, a, b, ha, hb, hxab⟩ := representative_doubleCoset_cover x
  have hrK : representative j ∈ K := by
    rw [hxab] at hx
    exact (K.mul_mem_cancel_left (hPK ha)).mp
      ((K.mul_mem_cancel_right (hPK hb)).mp hx)
  rcases hrep j with hrB | hrC | ⟨y, hy, hyne⟩
  · left
    rw [hxab]
    exact involutionMatrixLineStabilizer.mul_mem
      (involutionMatrixLineStabilizer.mul_mem (baseSubgroup_le_line ha) hrB)
      (baseSubgroup_le_line hb)
  · right
    rw [hxab]
    exact involutionMatrixSecondSubgroup.mul_mem
      (involutionMatrixSecondSubgroup.mul_mem (baseSubgroup_le_second ha) hrC)
      (baseSubgroup_le_second hb)
  · apply False.elim
    apply hyne
    have hyK := (sup_le hPK (Subgroup.zpowers_le.mpr hrK)) hy
    have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨y, hyK⟩ : K)))
    change y ^ Nat.card K = 1 at hh
    rwa [hK] at hh

/-- The checked double-coset sieve and two candidate divisibility obstructions
exclude every subgroup of order 6912, without a pair hypothesis. -/
public theorem order27Exclusion_of_certificates
    (hline : ¬ 6912 ∣ Nat.card involutionMatrixLineStabilizer)
    (hsecond : ¬ 6912 ∣ Nat.card involutionMatrixSecondSubgroup)
    (hrep : ∀ j : Fin 110,
      representative j ∈ involutionMatrixLineStabilizer ∨
      representative j ∈ involutionMatrixSecondSubgroup ∨
      ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative j), x ^ 6912 ≠ 1) :
    Order27Exclusion := by
  classical
  intro K hK
  let T₀ : Sylow 2 K := Classical.choice inferInstance
  let P : Subgroup MatrixGroup := T₀.toSubgroup.map K.subtype
  have hP : Nat.card P = 256 := by
    rw [← Nat.card_congr
      (T₀.toSubgroup.equivMapOfInjective K.subtype Subtype.val_injective).toEquiv]
    rw [T₀.card_eq_multiplicity, hK]
    decide +kernel
  let S : Sylow 2 MatrixGroup := Sylow.ofCard P (by
    rw [hP, involutionMatrixQuotient_card]
    decide +kernel)
  let T : Sylow 2 MatrixGroup := Sylow.ofCard baseSubgroup (by
    rw [baseSubgroup_card, involutionMatrixQuotient_card]
    decide +kernel)
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq MatrixGroup S T
  let L := K.map (MulAut.conj u).toMonoidHom
  have hPL : baseSubgroup ≤ L := by
    have h := Subgroup.map_mono (f := (MulAut.conj u).toMonoidHom)
      (show S.toSubgroup ≤ K from Subgroup.map_subtype_le _)
    have hu' : S.toSubgroup.map (MulAut.conj u).toMonoidHom = baseSubgroup :=
      congrArg Sylow.toSubgroup hu
    rwa [hu'] at h
  have hL : Nat.card L = 6912 :=
    (Nat.card_congr (K.equivMapOfInjective _ (MulAut.conj u).injective).toEquiv).symm.trans hK
  rcases overgroup_le_candidate hrep L hPL hL with hB | hC
  · exact hline (hL ▸ card_dvd_of_le hB)
  · exact hsecond (hL ▸ card_dvd_of_le hC)


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2
