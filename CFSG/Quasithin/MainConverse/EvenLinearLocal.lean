module

public import CFSG.Quasithin.MainConverse.EvenLinearLocal.BinaryRank
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.BinaryThree
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.BinaryHigherEven
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeRank
public import CFSG.Quasithin.MainConverse.Transport
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Local conditions for the even linear converse

The groups PSL₃(2^f), for every positive f, and PSL₄(2), PSL₅(2) satisfy
quasithinness and even characteristic. In dimension three every maximal
two-local is conjugate to a full point or line parabolic. Odd-primary
subgroups of these parabolics embed into GL₂, giving prime rank at most two;
their normal root planes are self-centralizing, giving characteristic two.
The binary higher-dimensional cases use odd-prime order bounds for QT and
self-centralizing block-unipotent radicals in geometric parabolics for E.

Transport through actual group isomorphisms preserves the arbitrary field
witness in `IsPSL`. These intrinsic calculations establish QT and E without
a proper-K premise, so they apply directly on the approved induction domain.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1–2), printed p.4, repeated as Theorem 0.1.1 on p.482.
-/

namespace CFSG.Quasithin.MainConverse

open scoped MatrixGroups

/-- All maximal two-locals of PSL₃(2^f) have odd-prime ranks at most two,
by conjugacy to the full projective point and line parabolics. -/
public theorem psl3_two_pow_quasithin_of_card
    {F : Type*} [Field F] [Finite F] {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2 ^ f) : IsQuasithin PSL(3, F) := by
  apply Theory.GroupTheory.isQuasithin_iff_maximalTwoLocal.mpr
  intro M hM p hp ho
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := LinearThreeGeometry.maximalTwoLocal_conjugate F hf hF M hM
  rw [Theory.GroupTheory.primeRank_equiv p
    (Subgroup.equivMapOfInjective M (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)]
  rcases hg with hg | hg
  · rw [hg]
    exact LinearThreeRank.pointParabolic_primeRank_le_two_of_card F hF ho
  · rw [hg]
    exact LinearThreeRank.lineParabolic_primeRank_le_two_of_card F hF ho

/-- QT for every actual PSL₃(2^f) model, including f = 1. -/
public theorem psl3_two_pow_quasithin {G : Type*} [Group G] [Finite G]
    {f : ℕ} (hf : 0 < f) (hG : ClassicalGroup.IsPSL G 3 (2 ^ f)) :
    IsQuasithin G := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hG
  exact Theory.GroupTheory.isQuasithin_of_equiv e.symm
    (psl3_two_pow_quasithin_of_card hf hcard)

/-- E for every actual PSL₃(2^f) model, using the intrinsic parabolic two-cores. -/
public theorem psl3_two_pow_evenCharacteristic {G : Type*} [Group G] [Finite G]
    {f : ℕ} (hf : 0 < f) (hG : ClassicalGroup.IsPSL G 3 (2 ^ f)) :
    IsEvenCharacteristic G := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hG
  exact evenCharacteristic_of_model_equiv e (LinearThreeGeometry.evenCharacteristic F hf hcard)

/-- The QT and E clauses of the generic linear case in Theorem 0.1.2(1). -/
public theorem psl3_two_pow_quasithin_and_evenCharacteristic
    {G : Type*} [Group G] [Finite G] {f : ℕ}
    (hf : 0 < f) (hG : ClassicalGroup.IsPSL G 3 (2 ^ f)) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨psl3_two_pow_quasithin hf hG, psl3_two_pow_evenCharacteristic hf hG⟩

public theorem psl3_two_evenCharacteristic {G : Type*} [Group G] [Finite G]
    (hG : ClassicalGroup.IsPSL G 3 2) : IsEvenCharacteristic G := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hG
  let : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard'
  exact evenCharacteristic_of_model_equiv
    (e.trans (Atlas.fieldEquivPSL 3 eF)) BinaryThree.evenCharacteristic

public theorem psl3_two_quasithin_and_evenCharacteristic
    {G : Type*} [Group G] [Finite G] (hG : ClassicalGroup.IsPSL G 3 2) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨binary_linear_quasithin (Or.inl rfl) hG, psl3_two_evenCharacteristic hG⟩

public theorem psl4_two_quasithin {G : Type*} [Group G] [Finite G]
    (hG : ClassicalGroup.IsPSL G 4 2) : IsQuasithin G :=
  binary_linear_quasithin (Or.inr (Or.inl rfl)) hG

public theorem psl5_two_quasithin {G : Type*} [Group G] [Finite G]
    (hG : ClassicalGroup.IsPSL G 5 2) : IsQuasithin G :=
  binary_linear_quasithin (Or.inr (Or.inr rfl)) hG

/-- The QT and E clauses of the linear cases in Theorem 0.1.2(2). -/
public theorem binary_higher_quasithin_and_evenCharacteristic
    {G : Type*} [Group G] [Finite G] {n : ℕ}
    (hn : n = 4 ∨ n = 5) (hG : ClassicalGroup.IsPSL G n 2) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨binary_linear_quasithin (Or.inr hn) hG, binary_higher_evenCharacteristic hn hG⟩

/-- Both source local conditions for PSL₄(2). -/
public theorem psl4_two_quasithin_and_evenCharacteristic
    {G : Type*} [Group G] [Finite G] (hG : ClassicalGroup.IsPSL G 4 2) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  binary_higher_quasithin_and_evenCharacteristic (Or.inl rfl) hG

/-- Both source local conditions for PSL₅(2). -/
public theorem psl5_two_quasithin_and_evenCharacteristic
    {G : Type*} [Group G] [Finite G] (hG : ClassicalGroup.IsPSL G 5 2) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  binary_higher_quasithin_and_evenCharacteristic (Or.inr rfl) hG

end CFSG.Quasithin.MainConverse
