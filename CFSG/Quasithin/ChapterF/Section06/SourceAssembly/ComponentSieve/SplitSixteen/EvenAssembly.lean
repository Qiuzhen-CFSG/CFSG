module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.SplitSixteen.EvenModels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.DihedralEight.ElementaryEight
public import Theory.GroupTheory.SplitDihedralElementary

/-!
# The actual even-field source constructors under C2 times D8

The order sieve leaves the small binary linear carriers. PSL2(16) has an
elementary Sylow using all sixteen ambient elements and is impossible.
The other exceptional endpoints are compared through their concrete
matrix and permutation isomorphisms. Thus the Bender constructors leave
PSL2(5) or PSL2(8), while rank-two constructors leave PSL2(7) or A6.

These reductions retain the literal quotient K/Z(K) in F.6.18(8)--(9),
printed p.310; the PSL2(8) extension argument is separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.SplitSixteen
variable {G : Type*} [Group G] [Finite G]

theorem binary_linear_three_parameters
    (P : Sylow 2 G) (hP : Nat.card P ≤ 16) {f : ℕ} (hf : 1 ≤ f)
    (hm : ClassicalGroup.IsPSL G 3 (2 ^ f)) : f = 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hd := Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card (F := F)
  rw [hF] at hd
  by_contra hn
  have hf2 : 2 ≤ f := by omega
  have h32 : 32 ∣ Nat.card G := by
    rw [Nat.card_congr e.toEquiv]
    apply dvd_trans _ hd
    rw [← pow_mul]
    exact Nat.pow_dvd_pow 2 (by omega : 5 ≤ f * 3)
  have hb := Nat.le_of_dvd (Nat.card_pos (α := P))
    (P.pow_dvd_card_of_pow_dvd_card (n := 5) h32)
  omega

theorem bender_models_of_sylow_le_sixteen
    (P : Sylow 2 G) (hP : Nat.card P ≤ 16)
    (hm : ClassificationModels.IsBenderModel G) :
    ClassicalGroup.IsPSL G 2 5 ∨ ClassicalGroup.IsPSL G 2 8 ∨
      ClassicalGroup.IsPSL G 2 16 := by
  cases hm with
  | linear f hf hm =>
    rcases binary_linear_two_parameters P hP hf hm with rfl | rfl | rfl
    · exact .inl (prime_five_model_of_binary_four hm)
    · exact .inr (.inl hm)
    · exact .inr (.inr hm)
  | unitary f hf hm => exact (not_unitary_three_binary_of_sylow_le_sixteen P hP hf hm).elim
  | suzuki m hm he => exact (not_suzuki_of_sylow_le_sixteen P hP hm he).elim

theorem rankTwo_models_of_sylow_le_sixteen
    (P : Sylow 2 G) (hP : Nat.card P ≤ 16) {f : ℕ}
    (hm : ChapterA.Section02.IsTheoremCRankTwoModel G f) :
    ClassicalGroup.IsPSL G 2 7 ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) := by
  cases hm with
  | linear hf hm =>
    have he := binary_linear_three_parameters P hP hf hm
    subst f
    exact .inl (prime_seven_model_of_binary_linear_three (by simpa using hm))
  | symplectic hf iso => exact (not_symplectic_of_sylow_le_sixteen P hP hf iso).elim
  | g2 hf iso => exact (not_g2_of_sylow_le_sixteen P hP hf iso).elim
  | triality hf iso => exact (not_triality_of_sylow_le_sixteen P hP hf iso).elim
  | ree_f4 m _ _ iso =>
      obtain ⟨e⟩ := iso
      exact (not_ree_f4_of_sylow_le_sixteen P hP m e).elim
  | symplectic_derived _ iso =>
      obtain ⟨e⟩ := iso
      exact .inr ⟨e.trans
        Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩
  | g2_derived _ iso =>
      obtain ⟨e⟩ := iso
      exact (not_g2_derived_of_sylow_le_sixteen P hP e).elim
  | tits _ iso =>
      obtain ⟨e⟩ := iso
      exact (not_tits_of_sylow_le_sixteen P hP e).elim

/-- The literal central quotient cannot be the elementary-Sylow PSL2(16). -/
theorem not_pslSixteen_central_quotient
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 16) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 4) (by
    change Fintype.card F = 16
    simpa only [Nat.card_eq_fintype_card] using hF)
  let P := Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.standardSylow F
  let a : Multiplicative F ≃* P :=
    (MonoidHom.ofInjective
      (Matrix.ProjectiveSpecialLinearGroup.OddBorel.unipotentHom_injective F)).trans
      (MulEquiv.subgroupCongr
        (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.coe_standardSylow F).symm)
  let : IsElementaryAbelian 2 (Multiplicative F) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Multiplicative.toAdd.injective
      simp [pow_two, CharTwo.add_self_eq_zero]) }
  let : IsElementaryAbelian 2 P :=
    IsElementaryAbelian.of_surjective a.toMonoidHom a.surjective
  have hP : Nat.card P = 16 := by
    rw [← Nat.card_congr a.toEquiv]
    exact hF
  exact not_elementary_sixteen_sylow_section T eT K
    (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
    (e.surjective.comp (QuotientGroup.mk'_surjective (center K))) P hP

/-- Complete source Bender reduction on the original component quotient. -/
theorem bender_central_quotient_of_split_sixteen
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) (hm : ClassificationModels.IsBenderModel (K ⧸ center K)) :
    ClassicalGroup.IsPSL (K ⧸ center K) 2 5 ∨ ClassicalGroup.IsPSL (K ⧸ center K) 2 8 := by
  let P : Sylow 2 (K ⧸ center K) := default
  have hP : Nat.card P ≤ 16 := by
    have hp := central_quotient_sylow_card_le T K P
    rwa [Nat.card_congr eT.toEquiv, split_sixteen_card] at hp
  rcases bender_models_of_sylow_le_sixteen P hP hm with hm | hm | hm
  · exact .inl hm
  · exact .inr hm
  · exact (not_pslSixteen_central_quotient T eT K hm).elim

end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.SplitSixteen
