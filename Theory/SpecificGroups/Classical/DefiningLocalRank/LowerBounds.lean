module
public import Theory.SpecificGroups.Classical.LinearFundamental
public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental
public import Theory.SpecificGroups.SL2.DefiningRank
public import Theory.Quasithin.LocalRank
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Positive defining-prime two-local rank in signed degree three

The genuine fundamental SL₂ embeds in each projective degree-three group.
Its scalar minus one is a nonidentity involution in odd characteristic, and
its root subgroup lies in that involution's centralizer. Thus the defining
field exponent is a lower bound on two-local rank. The unitary proof uses
the actual fixed field and transports the fundamental subgroup to the stored
Hermitian form, including defining prime three.

Source: Aschbacher–Smith A.2.17, pp.38–39; the nonnormal-component sieve in
A.1.34(3) and A.3.8(1–2), pp.29–30 and45–46, uses this local witness together
with the independent ordinary rank-two witness.
-/

public section
open Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Theory.SpecificGroups.DefiningLocalRank

/-- The fundamental SL₂ involution makes its defining-rank witness local. -/
theorem fieldExponent_le_localRank_of_sl2_embedding
    {F G : Type*} [Field F] [Finite F] [Group G] [Finite G]
    {p e : ℕ} [Fact p.Prime] [CharP F p] (hp : p ≠ 2)
    (hc : Nat.card F = p ^ e) (f : SL(2,F) →* G) (hf : Function.Injective f) :
    e ≤ twoLocalPrimeRank p G := by
  obtain ⟨hz,hz2⟩ := SpecialLinearGroup.map_neg_one_isInvolution hp f hf
  exact (SpecialLinearGroup.fieldExponent_le_primeRank_centralizer hc f hf).trans
    ((Theory.GroupTheory.isTwoLocal_involution_centralizer
      (orderOf_eq_prime hz2 hz)).primeRank_le p)

/-- The split ternary group has a fundamental defining-prime local witness. -/
theorem psl3_fieldExponent_le_twoLocalPrimeRank
    {F : Type*} [Field F] [Finite F] {p e : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hc : Nat.card F = p ^ e) :
    e ≤ twoLocalPrimeRank p PSL(3,F) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  let a : ProjectiveSpecialLinearGroup (Fin 2 ⊕ Fin 1) F ≃* PSL(3,F) :=
    SpecialLinearGroup.LinearFundamental.projectiveReindex finSumFinEquiv
  let f : SL(2,F) →* PSL(3,F) := a.toMonoidHom.comp
    (SpecialLinearGroup.LinearFundamental.projectLeft (n := Fin 1))
  exact fieldExponent_le_localRank_of_sl2_embedding hp hc f
    (a.injective.comp SpecialLinearGroup.LinearFundamental.projectLeft_injective)

/-- Every stored ternary Hermitian model has the same local witness. -/
theorem psu3_fieldExponent_le_twoLocalPrimeRank
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {p e : ℕ} [Fact p.Prime] (hp : Odd p) (he : 0 < e)
    (hc : Nat.card F = (p ^ e) ^ 2) (hj : ∀ x, J.conj x = x ^ (p ^ e)) :
    e ≤ twoLocalPrimeRank p (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hq : IsPrimePow (p ^ e) := (isPrimePow_nat_iff _).mpr
    ⟨p,e,Fact.out,he,rfl⟩
  obtain ⟨f,c,hf,-,-,-⟩ :=
    ClassicalUnitary.OddFundamental.exists_fundamental_complement (n := 1) J hq hp.pow hc hj
  have hk : Nat.card (FixedBy.subfield F J.conj) = p ^ e :=
    J.fixed_card_prime_power hq hc hj
  let : Fintype (FixedBy.subfield F J.conj) := Fintype.ofFinite _
  let : CharP (FixedBy.subfield F J.conj) p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp
  exact fieldExponent_le_localRank_of_sl2_embedding hp2 hk f hf

end Theory.SpecificGroups.DefiningLocalRank
