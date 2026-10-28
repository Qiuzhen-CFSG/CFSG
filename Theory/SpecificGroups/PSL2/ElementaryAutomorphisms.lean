module

public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.OuterInvolutions
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.Bounds
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.CyclicKernel

/-!
# Elementary automorphism actions and perfect central covers of binary PSL₂

Every abstract automorphism of the actual matrix quotient PSL₂(2ⁿ) is inner
followed by a field automorphism. Combining that coverage with the model bounds
gives a split homomorphism to the cyclic field-automorphism group whose kernel
is exactly the inner subgroup. Every elementary two-subgroup has order at most
2ⁿ when n ≥ 2; one disjoint from the inner subgroup has order at most two.
Its nonidentity members are inner-conjugate to the half-degree Frobenius, so n
is even. The additive trace has image the fixed field, of order 2^(n/2).

For a perfect central cover, the genuine quotient action is faithful and detects
innerness. Applying the model theorems to this action's actual image proves both
bounds for faithful elementary actors on the cover, and identifies their
nontrivial outer quotient actions with the specified field involution.

These are the automorphism facts used in GLS, Volume 2, Theorem 26.24, Step 5
and its final contradiction (`refs/KGroup/GLS2/ChapterG.tex`). The original
conditional transport APIs remain available, while the unconditional theorems
below discharge coverage and the model estimates. The whole component
normalization theorem additionally uses its separate representation arguments.
-/

namespace Theory.PSL2

variable {K L A : Type*} [Field K] [_root_.Group L] [_root_.Group A]

/-- A model bound transports to every faithful elementary action on a perfect
central cover. The elementary subgroup is the actual action image. -/
public theorem elementary_action_card_le_of_model_bound [_root_.Group.IsPerfect L]
    {p b : ℕ} [IsElementaryAbelian p A]
    (e : L ⧸ Subgroup.center L ≃* Group K)
    (ρ : A →* MulAut L) (hρ : Function.Injective ρ)
    (hbound : ∀ D : Subgroup (MulAut (Group K)),
      IsElementaryAbelian p D → Nat.card D ≤ b) : Nat.card A ≤ b := by
  let φ := (MulAut.centralQuotientAction e).comp ρ
  have hφ : Function.Injective φ := MulAut.centralQuotientAction_comp_injective e ρ hρ
  have hD : IsElementaryAbelian p φ.range :=
    IsElementaryAbelian.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hc : Nat.card φ.range = Nat.card A :=
    Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm
  simpa only [hc] using hbound φ.range hD

/-- Having no nonidentity inner actor passes to the faithful quotient image. -/
public theorem quotient_action_image_disjoint_inner [_root_.Group.IsPerfect L]
    (e : L ⧸ Subgroup.center L ≃* Group K) (ρ : A →* MulAut L)
    (hinner : ∀ x : A, (∃ y : L, ρ x = MulAut.conj y) → x = 1) :
    Disjoint ((MulAut.centralQuotientAction e).comp ρ).range (inner K) := by
  rw [Subgroup.disjoint_def]
  intro a ha hi
  obtain ⟨x, rfl⟩ := ha
  have hx := (MulAut.centralQuotientAction_inner_iff e (ρ x)).mp
    ((mem_inner_iff K _).mp hi)
  rw [hinner x hx, map_one]

end Theory.PSL2

namespace Theory.PSL2

section OuterQuotient

variable (K : Type*) [Field K] [CharP K 2] [Finite K]

/-- The field automorphisms identify the actual quotient Aut(PSL₂)/Inn(PSL₂). -/
public noncomputable def fieldOuterEquiv :
    (K ≃+* K) ≃* MulAut (Group K) ⧸ inner K :=
  fieldOuterEquivOfCoverage semilinear_coverage

/-- The field component of an arbitrary automorphism of characteristic-two PSL₂. -/
public noncomputable def fieldProjection : MulAut (Group K) →* (K ≃+* K) :=
  fieldProjectionOfCoverage semilinear_coverage

public theorem fieldProjection_fieldAut (σ : K ≃+* K) :
    fieldProjection K (fieldAut σ) = σ :=
  fieldProjectionOfCoverage_fieldAut semilinear_coverage σ

public theorem fieldProjection_split :
    (fieldProjection K).comp fieldAutHom = MonoidHom.id _ :=
  fieldProjectionOfCoverage_split semilinear_coverage

public theorem fieldProjection_surjective : Function.Surjective (fieldProjection K) :=
  fieldProjectionOfCoverage_surjective semilinear_coverage

public theorem fieldProjection_ker : (fieldProjection K).ker = inner K :=
  fieldProjectionOfCoverage_ker semilinear_coverage

/-- The outer quotient is cyclic, with arbitrary-automorphism coverage discharged. -/
public theorem outer_isCyclic : IsCyclic (MulAut (Group K) ⧸ inner K) :=
  outer_isCyclic_of_coverage semilinear_coverage

/-- An elementary two-subgroup with trivial inner intersection has order at most two. -/
public theorem elementary_disjoint_inner_card_le_two
    (D : Subgroup (MulAut (Group K))) [IsElementaryAbelian 2 D]
    (hD : Disjoint D (inner K)) : Nat.card D ≤ 2 :=
  elementary_card_le_two_of_disjoint_inner semilinear_coverage D hD

end OuterQuotient

/-- Every elementary two-subgroup of Aut(PSL₂(2ⁿ)) has order at most 2ⁿ.
This is the model estimate used in GLS2, Theorem 26.24, Step 5. -/
public theorem elementary_card_le {n : ℕ} (hn : 2 ≤ n)
    (D : Subgroup (MulAut (BinaryGroup n))) [IsElementaryAbelian 2 D] :
    Nat.card D ≤ 2 ^ n :=
  elementary_card_le_of_coverage hn (binary_semilinear_coverage hn) D

/-- Every outer involution is inner-conjugate to the actual half-degree
Frobenius. In particular, outer involutions force even field degree. -/
public theorem outer_involution_halfFrobenius {n : ℕ} (hn : 2 ≤ n)
    (a : MulAut (BinaryGroup n)) (ha : a ^ 2 = 1)
    (houter : a ∉ inner (BinaryField n)) :
    Even n ∧ orderOf (binaryHalfFrobenius n) = 2 ∧
      (∀ x : BinaryField n, binaryHalfFrobenius n x = x ^ (2 ^ (n / 2))) ∧
      ∃ c : BinaryGroup n,
        MulAut.congr (MulAut.conj c) (fieldAut (binaryHalfFrobenius n)) = a :=
  outer_involution_halfFrobenius_of_coverage hn (binary_semilinear_coverage hn) a ha houter

/-- The nonidentity actors in an elementary subgroup disjoint from the inner
subgroup are conjugate to the distinguished field involution. -/
public theorem elementary_disjoint_inner_nonidentity_halfFrobenius {n : ℕ} (hn : 2 ≤ n)
    (D : Subgroup (MulAut (BinaryGroup n))) [IsElementaryAbelian 2 D]
    (hD : Disjoint D (inner (BinaryField n)))
    (a : MulAut (BinaryGroup n)) (ha : a ∈ D) (hne : a ≠ 1) :
    Even n ∧ orderOf (binaryHalfFrobenius n) = 2 ∧
      (∀ x : BinaryField n, binaryHalfFrobenius n x = x ^ (2 ^ (n / 2))) ∧
      ∃ c : BinaryGroup n,
        MulAut.congr (MulAut.conj c) (fieldAut (binaryHalfFrobenius n)) = a :=
  outer_involution_halfFrobenius hn a
    (elemPow_eq_one_of_isElementaryAbelian a ha)
    (fun hi => hne (Subgroup.disjoint_def.mp hD ha hi))

/-- The field involution has a fixed field of square-root order, and its
additive trace has exactly that image. This is the actual field-action
calculation underlying the source's outer-involution argument. -/
public theorem binaryHalfFrobenius_additive_action {n : ℕ} (hn : 0 < n) (heven : Even n) :
    orderOf (fieldAut (binaryHalfFrobenius n)) = 2 ∧
      Nat.card (FixedBy.subfield (BinaryField n) (binaryHalfFrobenius n)) = 2 ^ (n / 2) ∧
      ∀ x : BinaryField n,
        binaryHalfFrobenius n x = x ↔ ∃ y : BinaryField n, y + binaryHalfFrobenius n y = x := by
  have ho := binaryHalfFrobenius_order hn heven
  have hs : (binaryHalfFrobenius n) ^ 2 = 1 := by
    simpa only [ho] using pow_orderOf_eq_one (binaryHalfFrobenius n)
  have hs' : Function.Involutive (binaryHalfFrobenius n) :=
    fun x => DFunLike.congr_fun hs x
  have hne : binaryHalfFrobenius n ≠ RingEquiv.refl _ := by
    change binaryHalfFrobenius n ≠ 1
    intro h
    simp [h] at ho
  exact ⟨(orderOf_fieldAut _).trans ho, binary_fixedField_card hn _ hs' hne,
    fixed_iff_exists_add_conjugate _ hs' hne⟩

section PerfectCover

variable {L A : Type*} [_root_.Group L] [_root_.Group A]
    [_root_.Group.IsPerfect L] [IsElementaryAbelian 2 A]

/-- The Step 5 bound for the literal faithful action on a perfect central
cover of PSL₂(2ⁿ), including every quasisimple cover. -/
public theorem elementary_action_card_le {n : ℕ} (hn : 2 ≤ n)
    (e : L ⧸ Subgroup.center L ≃* BinaryGroup n)
    (ρ : A →* MulAut L) (hρ : Function.Injective ρ) : Nat.card A ≤ 2 ^ n :=
  elementary_action_card_le_of_model_bound e ρ hρ fun D hD =>
    @elementary_card_le n hn D hD

/-- The final-contradiction bound for a faithful elementary action on a perfect
cover when no nonidentity actor induces an inner automorphism. -/
public theorem elementary_action_card_le_two_of_no_inner {n : ℕ}
    (e : L ⧸ Subgroup.center L ≃* BinaryGroup n)
    (ρ : A →* MulAut L) (hρ : Function.Injective ρ)
    (hinner : ∀ x : A, (∃ y : L, ρ x = MulAut.conj y) → x = 1) : Nat.card A ≤ 2 := by
  let φ := (MulAut.centralQuotientAction e).comp ρ
  have hφ : Function.Injective φ := MulAut.centralQuotientAction_comp_injective e ρ hρ
  let : IsElementaryAbelian 2 φ.range :=
    IsElementaryAbelian.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hc : Nat.card A = Nat.card φ.range :=
    Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
  rw [hc]
  exact elementary_disjoint_inner_card_le_two (BinaryField n) φ.range
    (quotient_action_image_disjoint_inner e ρ hinner)

/-- Each nonidentity actor in the no-inner case induces, on the specified
central quotient, an inner conjugate of the actual order-two field action. -/
public theorem elementary_action_nonidentity_halfFrobenius {n : ℕ} (hn : 2 ≤ n)
    (e : L ⧸ Subgroup.center L ≃* BinaryGroup n)
    (ρ : A →* MulAut L) (hρ : Function.Injective ρ)
    (hinner : ∀ x : A, (∃ y : L, ρ x = MulAut.conj y) → x = 1)
    (x : A) (hx : x ≠ 1) :
    Even n ∧ orderOf (binaryHalfFrobenius n) = 2 ∧
      (∀ t : BinaryField n, binaryHalfFrobenius n t = t ^ (2 ^ (n / 2))) ∧
      ∃ c : BinaryGroup n,
        MulAut.congr (MulAut.conj c) (fieldAut (binaryHalfFrobenius n)) =
          MulAut.centralQuotientAction e (ρ x) := by
  let φ := (MulAut.centralQuotientAction e).comp ρ
  have hφ : Function.Injective φ := MulAut.centralQuotientAction_comp_injective e ρ hρ
  let : IsElementaryAbelian 2 φ.range :=
    IsElementaryAbelian.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  exact elementary_disjoint_inner_nonidentity_halfFrobenius hn φ.range
    (quotient_action_image_disjoint_inner e ρ hinner) (φ x) ⟨x, rfl⟩
    (fun h => hx (hφ (h.trans (map_one φ).symm)))

end PerfectCover

end Theory.PSL2
