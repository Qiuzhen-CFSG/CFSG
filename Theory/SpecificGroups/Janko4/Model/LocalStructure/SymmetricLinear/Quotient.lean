module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Model
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.Projection
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound
public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The two-core quotient of the literal J₄ max4 subgroup

The target group S₅ × SL₃(2) has order 20160 and trivial two-core. Thus a
surjection onto this target whose kernel is a two-group identifies the kernel
with the source two-core. For the literal matrix-word subgroup `max4Subgroup`,
the kernel condition follows from a local order-divisibility certificate
`Nat.card max4Subgroup ∣ 2^n * 20160`; the first isomorphism theorem then gives
the quotient comparison, with its value on every quotient representative.

The imported `Projection` constructs the epimorphism from the actual
112-dimensional matrices, and `OrderBound` certifies local order divisibility
through their full invariant filtration. These discharge both premises and
give the unconditional `max4QuotientEquiv`. Its representative formula agrees
with the actual matrix actions, including on the two literal ATLAS outputs.
No global J₄ order, simplicity or placement assertion is used.

Source context: Aschbacher–Smith, Proposition 1.3.4, printed p.511/PDF p.528
of `refs/quasithin.pdf`, citing Aschbacher (1986). The exact ATLAS subgroup
program and its provenance are retained beside `SymmetricLinear.Model`.
-/

public section

open Subgroup
namespace Janko4.LocalStructure.SymmetricLinear

/-- The order of the actual product model. -/
theorem quotientModel_card : Nat.card QuotientModel = 20160 := by
  rw [Nat.card_prod, Atlas.Comparisons.Exceptional.sl3Two_card]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem symmetricFive_twoCore : pCore 2 (Equiv.Perm (Fin 5)) = ⊥ := by
  by_contra hn
  have hnt : Nontrivial (pCore 2 (Equiv.Perm (Fin 5))) :=
    (nontrivial_iff_ne_bot _).mpr hn
  have hle := Equiv.Perm.alternatingGroup_le_of_normal
    (by simp : 5 ≤ Nat.card (Fin 5)) hnt
  have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hd : 3 ∣ Nat.card (pCore 2 (Equiv.Perm (Fin 5))) :=
    (by decide : 3 ∣ 60).trans (hc ▸ card_dvd_of_le hle)
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Equiv.Perm (Fin 5))).exists_card_eq
  rw [hn] at hd
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

private theorem slThree_twoCore :
    pCore 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  rcases (inferInstance : (pCore 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))).Normal).eq_bot_or_eq_top with h | h
  · exact h
  have hp : IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    pCore_isPGroup.of_equiv ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [Atlas.Comparisons.Exceptional.sl3Two_card] at hn
  have hd : 3 ∣ 2 ^ n := by rw [← hn]; decide
  exact False.elim ((by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd))

/-- Both factors, and hence their product, have trivial two-core. -/
theorem quotientModel_twoCore : pCore 2 QuotientModel = ⊥ := by
  rw [pCore_prod, symmetricFive_twoCore, slThree_twoCore, bot_prod_bot]

/-- Cancelling the actual image order leaves a power-of-two bound on the kernel. -/
theorem max4_kernel_isTwoGroup_of_card_dvd
    (f : max4Subgroup →* QuotientModel) (hf : Function.Surjective f)
    {n : ℕ} (hc : Nat.card max4Subgroup ∣ 2 ^ n * 20160) :
    IsPGroup 2 f.ker := by
  have hcount := f.ker.card_mul_index
  rw [index_ker, f.range_eq_top_of_surjective hf, card_top, quotientModel_card] at hcount
  rw [← hcount] at hc
  exact IsPGroup.of_card_dvd_pow ((Nat.mul_dvd_mul_iff_right (by decide : 0 < 20160)).mp hc)

/-- The kernel is the full two-core when the matrix epimorphism has two-group kernel. -/
theorem max4_kernel_eq_twoCore_of_surjective
    (f : max4Subgroup →* QuotientModel) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : f.ker = pCore 2 max4Subgroup := by
  have he := f.comap_pCore_of_ker_isPGroup hf hk
  rw [quotientModel_twoCore] at he
  exact he

/-- Quotient comparison for any concrete epimorphism and local count. -/
noncomputable def max4QuotientEquivOfSurjectiveOfCardDvd
    (f : max4Subgroup →* QuotientModel) (hf : Function.Surjective f)
    {n : ℕ} (hc : Nat.card max4Subgroup ∣ 2 ^ n * 20160) :
    (max4Subgroup ⧸ pCore 2 max4Subgroup) ≃* QuotientModel :=
  (QuotientGroup.quotientMulEquivOfEq
    (max4_kernel_eq_twoCore_of_surjective f hf
      (max4_kernel_isTwoGroup_of_card_dvd f hf hc)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The comparison agrees with the supplied map on the literal quotient projection. -/
theorem max4QuotientEquivOfSurjectiveOfCardDvd_apply
    (f : max4Subgroup →* QuotientModel) (hf : Function.Surjective f)
    {n : ℕ} (hc : Nat.card max4Subgroup ∣ 2 ^ n * 20160) (g : max4Subgroup) :
    max4QuotientEquivOfSurjectiveOfCardDvd f hf hc
      (QuotientGroup.mk' (pCore 2 max4Subgroup) g) = f g := by
  rfl

/-- The certified local order bound makes the actual projection kernel a two-group. -/
theorem max4Projection_kernel_isTwoGroup : IsPGroup 2 max4Projection.ker := by
  obtain ⟨n, hn⟩ := max4_card_dvd_twoPower_mul
  exact max4_kernel_isTwoGroup_of_card_dvd max4Projection max4Projection_surjective hn

/-- The actual five-point and section actions have exactly the intrinsic two-core
as their common kernel. -/
theorem max4Projection_kernel_eq_twoCore :
    max4Projection.ker = pCore 2 max4Subgroup :=
  max4_kernel_eq_twoCore_of_surjective max4Projection max4Projection_surjective
    max4Projection_kernel_isTwoGroup

/-- The two-core quotient of the literal ATLAS matrix-word subgroup is
S₅ × SL₃(2), via its certified five-point and binary-section actions. -/
noncomputable def max4QuotientEquiv :
    (max4Subgroup ⧸ pCore 2 max4Subgroup) ≃* QuotientModel :=
  (QuotientGroup.quotientMulEquivOfEq max4Projection_kernel_eq_twoCore.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective max4Projection max4Projection_surjective)

/-- The quotient comparison descends the actual matrix projection. -/
theorem max4QuotientEquiv_apply (g : max4Subgroup) :
    max4QuotientEquiv (QuotientGroup.mk' (pCore 2 max4Subgroup) g) =
      max4Projection g := by
  rfl

/-- The quotient image of the first literal ATLAS output. -/
theorem max4QuotientEquiv_first :
    max4QuotientEquiv (QuotientGroup.mk' (pCore 2 max4Subgroup) Projection.first) =
      Projection.firstImage := by
  rw [max4QuotientEquiv_apply, max4Projection_first]

/-- The quotient image of the second literal ATLAS output. -/
theorem max4QuotientEquiv_second :
    max4QuotientEquiv (QuotientGroup.mk' (pCore 2 max4Subgroup) Projection.second) =
      Projection.secondImage := by
  rw [max4QuotientEquiv_apply, max4Projection_second]

end Janko4.LocalStructure.SymmetricLinear
