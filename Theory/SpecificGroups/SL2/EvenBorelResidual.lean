module

public import Theory.SpecificGroups.SL2.ProjectiveBorelFrobenius
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Residuals and the torus quotient of even projective SL₂ Borels

The standard upper-unipotent subgroup is Sylow, and its normalizer is the
actual upper triangular projective Borel. Sylow conjugacy therefore identifies
the Borel at any specified Sylow two-subgroup. Its unipotent radical is its
two-core, and the diagonal complement constructs a multiplicative equivalence
from the quotient to the field's unit group. For q ≥ 4 the Borel is two-perfect.
Its torus contains a factor three exactly in even field degree; the entire
Borel has three-prime order in odd degree.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954. The matrix,
complement and two-perfectness arguments reuse the existing SL₂ APIs.
-/

@[expose] public section

open scoped MatrixGroups
open Subgroup BenderSuzuki.Converse Matrix.SpecialLinearGroup
namespace Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
open OddBorel
variable (F : Type*) [Field F] [CharP F 2]

noncomputable def torusEquiv : Fˣ ≃* complement F :=
  MonoidHom.ofInjective
    ((pi_injective (F := F)).comp (torHom_injective (F := F)))

theorem card_torus [Finite F] : Nat.card (complement F) = Nat.card F - 1 := by
  rw [← Nat.card_congr (torusEquiv F).toEquiv, Nat.card_units]

noncomputable def rankOneBorelEquiv : rankOneBorel F ≃* borel F := by
  have h : rankOneBorel F = Borel F := by
    ext g
    exact (mem_rankOneBorel_iff g).trans (mem_Borel_iff g).symm
  have hm : (rankOneBorel F).map (pi F) = borel F := by
    rw [h, borel_eq_PBorel, PBorel_eq_map]
  exact (equivMapOfInjective _ _ (pi_injective (F := F))).trans (MulEquiv.subgroupCongr hm)

variable [Finite F]

omit [Finite F] [CharP F 2] in
theorem upperUnipotent_map : (upperUnipotent F).map (pi F) = kernel F := by
  have h : upperUnipotentHom F = uniHom F := by
    apply MonoidHom.ext
    intro t
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperUnipotentHom, transvection_coe, uniHom]
  rw [upperUnipotent, h, kernel, unipotentHom, MonoidHom.range_comp]

noncomputable def standardSylow : Sylow 2 PSL(2,F) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (upperUnipotentSylow F 2).mapSurjective (pi_surjective (F := F))

theorem coe_standardSylow : (standardSylow F : Subgroup PSL(2,F)) = kernel F := by
  change (upperUnipotent F).map (pi F) = _
  exact upperUnipotent_map F

omit [Finite F] in
theorem normalizer_kernel : normalizer (kernel F : Set PSL(2,F)) = borel F := by
  rw [← upperUnipotent_map,
    ← map_normalizer_eq_of_bijective (upperUnipotent F)
      ⟨pi_injective (F := F), pi_surjective (F := F)⟩]
  change (rankOneBorel F).map (pi F) = _
  have h : rankOneBorel F = Borel F := by
    ext g
    exact (mem_rankOneBorel_iff g).trans (mem_Borel_iff g).symm
  rw [h, borel_eq_PBorel, PBorel_eq_map]

theorem sylow_normalizer_conjugate (S : Sylow 2 PSL(2,F)) :
    ∃ g : PSL(2,F),
      (kernel F).map (MulAut.conj g).toMonoidHom = (S : Subgroup PSL(2,F)) ∧
      (borel F).map (MulAut.conj g).toMonoidHom = normalizer (S : Set PSL(2,F)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2,F) (standardSylow F) S
  have he : (kernel F).map (MulAut.conj g).toMonoidHom = (S : Subgroup PSL(2,F)) := by
    rw [← coe_standardSylow]
    exact congrArg Sylow.toSubgroup hg
  refine ⟨g, he, ?_⟩
  rw [← normalizer_kernel, map_equiv_normalizer_eq, he]
  rfl

noncomputable def sylowNormalizerEquiv (S : Sylow 2 PSL(2,F)) :
    normalizer (S : Set PSL(2,F)) ≃* borel F := by
  classical
  let g := Classical.choose (sylow_normalizer_conjugate F S)
  have hg := (Classical.choose_spec (sylow_normalizer_conjugate F S)).2
  exact ((equivMapOfInjective (borel F) (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hg)).symm

theorem card_borel : Nat.card (borel F) = Nat.card F * (Nat.card F - 1) := by
  rw [← (kernel_isComplement F).card_mul_card, card_kernel_in_borel,
    Nat.card_congr (subgroupOfEquivOfLe (show complement F ≤ borel F from le_sup_right)).toEquiv,
    card_torus]

theorem borel_isPPerfect (hq : 4 ≤ Nat.card F) : IsPPerfect 2 (borel F) :=
  (rankOneBorel_isPPerfect hq).of_surjective (rankOneBorelEquiv F).toMonoidHom
    (rankOneBorelEquiv F).surjective

theorem borel_twoResidual (hq : 4 ≤ Nat.card F) : pResidual 2 (borel F) = ⊤ :=
  (pResidual_eq_top_iff _ _).mpr (borel_isPPerfect F hq)

theorem twoCore_eq_kernel {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    pCore 2 (borel F) = (kernel F).subgroupOf (borel F) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsPGroup 2 ((kernel F).subgroupOf (borel F)) :=
    IsPGroup.of_card (n := n) (by rw [card_kernel_in_borel, hF])
  have hn : n ≠ 0 := by
    intro hn
    have hlarge : 1 < Nat.card F := Finite.one_lt_card
    simp [hF, hn] at hlarge
  have hi : ¬ 2 ∣ ((kernel F).subgroupOf (borel F)).index := by
    rw [(kernel_isComplement F).symm.index_eq_card,
      Nat.card_congr (subgroupOfEquivOfLe (show complement F ≤ borel F from le_sup_right)).toEquiv,
      card_torus, hF]
    have hm : (2 : ℕ) ^ n % 2 = 0 := by simp [Nat.pow_mod, hn]
    have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    omega
  exact le_antisymm (pCore_isPGroup.le_sylow_of_normal (hU.toSylow hi))
    (le_sSup ⟨inferInstance, hU⟩)

noncomputable def quotientTorusEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    borel F ⧸ pCore 2 (borel F) ≃* Fˣ :=
  (QuotientGroup.quotientMulEquivOfEq (twoCore_eq_kernel F hF)).trans
    ((kernel_isComplement F).symm.QuotientMulEquiv.trans
      ((subgroupOfEquivOfLe (show complement F ≤ borel F from le_sup_right)).trans
        (torusEquiv F).symm))

theorem card_quotient_twoCore {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card (borel F ⧸ pCore 2 (borel F)) = 2 ^ n - 1 := by
  rw [Nat.card_congr (quotientTorusEquiv F hF).toEquiv, Nat.card_units, hF]

theorem borel_threePrime_of_odd {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : Odd n) :
    Nat.Coprime 3 (Nat.card (borel F)) := by
  rw [card_borel, hF]
  exact ((by decide : Nat.Coprime 3 2).pow_right n).mul_right
    (Nat.BinaryTorusParity.coprime_three_sub_one hn)

theorem three_dvd_card_torus_iff {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    3 ∣ Nat.card (complement F) ↔ Even n := by
  rw [card_torus, hF, Nat.BinaryTorusParity.three_dvd_sub_one_iff]

end Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
