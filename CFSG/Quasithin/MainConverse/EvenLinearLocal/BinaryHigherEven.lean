module

public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.MainConverse.Transport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Even characteristic of PSL₄(2) and PSL₅(2)

A nonidentity two-subgroup of the binary linear group has a nonzero proper
fixed subspace. Its normalizer lies in the corresponding geometric parabolic.
That parabolic is the normalizer of its nonidentity block-unipotent radical,
so maximality among two-locals identifies the original maximal local with the
parabolic. The radical is self-centralizing and normal relative to this local;
its inclusion in the intrinsic two-core proves the required centralizer bound.

Over the binary field every invertible matrix has determinant one and the
special linear center is trivial. We use the actual quotient projection and
entrywise finite-field transport to retain the arbitrary field in `IsPSL`.
The argument needs no simplicity, quasithinness, or K-group assumption.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(2), printed p.4, repeated as Theorem 0.1.1(2), printed p.482;
condition E is defined on printed pp.3 and 481. Only the E clause is proved
here; the QT clauses are in `EvenLinearLocal.BinaryRank`.
-/

open scoped MatrixGroups

namespace CFSG.Quasithin.MainConverse.BinaryHigherEven

private theorem binary_center_eq_bot {n : ℕ} (hn : 0 < n) :
    Subgroup.center SL(n, ZMod 2) = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  change g = 1
  obtain ⟨a, ha, hga⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have ha0 : a ≠ 0 := by
    intro hzero
    simp [hzero, hn.ne'] at ha
  have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
  apply Subtype.ext
  simpa [ha1] using hga.symm

private noncomputable def projectiveEquivSL {n : ℕ} (hn : 0 < n) :
    PSL(n, ZMod 2) ≃* SL(n, ZMod 2) :=
  (MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center SL(n, ZMod 2)))
    ⟨by rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', binary_center_eq_bot hn],
      QuotientGroup.mk'_surjective _⟩).symm

private theorem binary_toGL_surjective (n : ℕ) :
    Function.Surjective (Matrix.SpecialLinearGroup.toGL :
      SL(n, ZMod 2) →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
  intro g
  have hu : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
  have hd : Matrix.det (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 :=
    congrArg Units.val (hu (Matrix.GeneralLinearGroup.det g))
  exact ⟨⟨g, hd⟩, Units.ext rfl⟩

private noncomputable def slEquivLinear (n : ℕ) :
    SL(n, ZMod 2) ≃* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :=
  (MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, binary_toGL_surjective n⟩).trans
    (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2)))

private theorem linear_evenCharacteristic {n : ℕ} (hn : 0 < n) :
    IsEvenCharacteristic (BinaryLinear.GL (Fin n → ZMod 2)) := by
  intro _ M hM _
  obtain ⟨Q, hQ, hQtwo, hQM⟩ := hM.1
  let W := BinaryLinear.fixedSpace Q
  have hV : 2 ∣ Nat.card (Fin n → ZMod 2) := by
    simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    exact dvd_pow_self 2 hn.ne'
  have hW : W ≠ ⊥ := BinaryLinear.fixedSpace_ne_bot hV hQtwo
  have hWt : W ≠ ⊤ := BinaryLinear.fixedSpace_ne_top hQ
  have hMP : M ≤ BinaryLinear.parabolic W := by
    rw [hQM]
    exact BinaryLinear.normalizer_le_parabolic_fixedSpace Q
  have hP : IsTwoLocal (BinaryLinear.parabolic W) :=
    ⟨BinaryLinear.radical W, BinaryLinear.radical_ne_bot hW hWt,
      BinaryLinear.radical_two W, (BinaryLinear.normalizer_radical hW).symm⟩
  have heq : M = BinaryLinear.parabolic W := le_antisymm hMP (hM.2 hP hMP)
  rw [heq]
  exact BinaryLinear.centralizer_parabolic_twoCore_le hW hWt

end CFSG.Quasithin.MainConverse.BinaryHigherEven

namespace CFSG.Quasithin.MainConverse

open BinaryHigherEven

/-- The binary rank-three and rank-four linear cases satisfy source condition E. -/
public theorem binary_higher_evenCharacteristic {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hG : ClassicalGroup.IsPSL G n 2) :
    IsEvenCharacteristic G := by
  have hnpos : 0 < n := by rcases hn with rfl | rfl <;> decide
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hG
  let : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard'
  let : Finite (BinaryLinear.GL (Fin n → ZMod 2)) :=
    Finite.of_injective (slEquivLinear n).symm (slEquivLinear n).symm.injective
  exact evenCharacteristic_of_model_equiv
    (e.trans ((Atlas.fieldEquivPSL n eF).trans
      ((projectiveEquivSL hnpos).trans (slEquivLinear n))))
    (linear_evenCharacteristic hnpos)

/-- The source E clause for PSL₄(2), with its arbitrary field witness. -/
public theorem psl4_two_evenCharacteristic {G : Type*} [Group G] [Finite G]
    (hG : ClassicalGroup.IsPSL G 4 2) : IsEvenCharacteristic G :=
  binary_higher_evenCharacteristic (Or.inl rfl) hG

/-- The source E clause for PSL₅(2), with its arbitrary field witness. -/
public theorem psl5_two_evenCharacteristic {G : Type*} [Group G] [Finite G]
    (hG : ClassicalGroup.IsPSL G 5 2) : IsEvenCharacteristic G :=
  binary_higher_evenCharacteristic (Or.inr rfl) hG

end CFSG.Quasithin.MainConverse
