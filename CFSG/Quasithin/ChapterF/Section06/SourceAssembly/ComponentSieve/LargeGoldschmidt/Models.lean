module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.ExponentEight
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.EvenThirtyTwo
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.Sporadic
/-!
# The complete catalogue under large exponent-eight Sylow data

The actual order-eight witness eliminates binary rank one, low-dimensional
linear and unitary groups, Suzuki groups and A₈. Order bounds eliminate the
remaining large even families. The odd rank-one Sylow rotation is too large
for exponent eight. Thus Theorem C leaves only odd prime degree-three groups
and M12, M22, M23 or J2. With Sylow order 64 only M12 survives sporadically.

This retains the genuine order-128 alternatives: their exclusion requires
additional marked local data. Source: Aschbacher–Smith F.6.18, printed p.310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.LargeGoldschmidt
open CFSG.Quasithin.ClassificationModels
open CFSG.Quasithin.ChapterA.Section02
variable {G : Type*} [Group G] [Finite G]
private theorem not256_of_le128 (P : Sylow 2 G) (hP : Nat.card P ≤ 128) : ¬256 ∣ Nat.card G := by
  intro hd
  have hh := Nat.le_of_dvd (Nat.card_pos (α := P))
    (P.pow_dvd_card_of_pow_dvd_card (n := 8) hd)
  norm_num at hh
  omega
private theorem large_sylow_thirty_two_dvd (P : Sylow 2 G) (hP : 32 ≤ Nat.card P) :
    32 ∣ Nat.card G := by
  obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
  have h5 : 5 ≤ n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact hn ▸ hP
  have hd : 32 ∣ Nat.card P := by rw [hn]; exact pow_dvd_pow 2 h5
  exact hd.trans P.card_subgroup_dvd_card
private theorem binary_power256 {f d : ℕ} (h : 8 ≤ f*d) : 256 ∣ (2^f)^d := by
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 h

theorem unitary_three_of_rankTwo_small_sylow_order_eight
    (P : Sylow 2 G) (hlo : 32 ≤ Nat.card P) (hhi : Nat.card P ≤ 128)
    (x : P) (hx : orderOf x = 8) {f : ℕ} (hm : IsTheoremCRankTwoModel G f) :
    ClassicalGroup.IsPSU G 3 3 := by
  have hn256 := not256_of_le128 P hhi
  have h32 := large_sylow_thirty_two_dvd P hlo
  cases hm with
  | linear _ hm => exact (not_binary_small_linear_of_sylow_order_eight P x hx (by decide : 3 ≤ 4) hm).elim
  | symplectic hf hm =>
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hc
    apply (hn256 _).elim
    rw [Nat.card_congr e.toEquiv,
      ← Nat.card_congr (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_sp,hc]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (binary_power256 (by omega)) _) _
  | g2 hf hm =>
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
    apply (hn256 _).elim
    rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hc]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (binary_power256 (by omega)) _) _
  | triality hf hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G f hf).mp hm
    apply (hn256 _).elim
    rw [Nat.card_congr e.toEquiv]
    apply dvd_trans _ (Triality.Standard.Parabolics.unipotent
      (Triality.Standard.binaryParameters f hf)).card_subgroup_dvd_card
    rw [Triality.Standard.Parabolics.card_unipotent_binary _ rfl]
    exact binary_power256 (f := f) (d := 12) (by omega)
  | ree_f4 m _ _ he =>
    obtain ⟨e⟩ := he
    apply (hn256 _).elim
    rw [Nat.card_congr e.toEquiv]
    apply dvd_trans _ (ReeF4.Parabolics.unipotent m).card_subgroup_dvd_card
    rw [ReeF4.Parabolics.card_unipotent]
    exact binary_power256 (by omega)
  | symplectic_derived _ he =>
    obtain ⟨e⟩ := he
    have j := e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
    rw [Nat.card_congr j.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at h32
    norm_num at h32
  | g2_derived _ he =>
    obtain ⟨e⟩ := he
    obtain ⟨j⟩ := Atlas.G2.nonempty_commutator_binary_equiv_psu3
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    refine ⟨GaloisField 3 2,inferInstance,inferInstance,ABG.unitaryForm 3 3 1 (by decide),?_,?_,⟨e.trans j⟩⟩
    · exact GaloisField.card 3 2 (by decide)
    · intro x
      rfl
  | tits _ he =>
    obtain ⟨e⟩ := he
    apply (hn256 _).elim
    rw [Nat.card_congr e.toEquiv,Tits.parrottGroup_card]
    norm_num

theorem no_bender_of_sylow_order_eight (P : Sylow 2 G) (x : P) (hx : orderOf x = 8) :
    ¬ IsBenderModel G := by
  intro hm
  cases hm with
  | linear f _ hm => exact not_binary_small_linear_of_sylow_order_eight P x hx (by decide : 2 ≤ 4) hm
  | unitary f _ hm => exact not_binary_unitary_three_of_sylow_order_eight P x hx hm
  | suzuki m hm he => exact not_suzuki_of_sylow_order_eight P x hx (by omega) he

theorem no_binary_four_five_of_small_sylow_order_eight
    (P : Sylow 2 G) (hhi : Nat.card P ≤ 128) (x : P) (hx : orderOf x = 8)
    {n : ℕ} (hn : n = 4 ∨ n = 5) : ¬ ClassicalGroup.IsPSL G n 2 := by
  rcases hn with rfl|rfl
  · exact not_binary_small_linear_of_sylow_order_eight P x hx (f := 1) (by decide)
  rintro ⟨F,_,_,hc,⟨e⟩⟩
  apply not256_of_le128 P hhi
  rw [Nat.card_congr e.toEquiv]
  have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
  rw [hc] at hh
  norm_num [Fin.prod_univ_succ] at hh
  rw [hh]
  norm_num

theorem no_alternating_le_eight_of_large_sylow_order_eight
    (P : Sylow 2 G) (hlo : 32 ≤ Nat.card P) (x : P) (hx : orderOf x = 8)
    {n : ℕ} (hn : n ≤ 8) : ¬ Nonempty (G ≃* alternatingGroup (Fin n)) := by
  by_cases hn8 : n=8
  · subst n
    exact not_alternating_eight_of_sylow_order_eight P x hx
  rintro ⟨e⟩
  have hd : 32 ∣ Nat.card (Equiv.Perm (Fin n)) := by
    have hh := large_sylow_thirty_two_dvd P hlo
    rw [Nat.card_congr e.toEquiv] at hh
    exact hh.trans (alternatingGroup (Fin n)).card_subgroup_dvd_card
  simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] at hd
  have hn7 : n ≤ 7 := by omega
  interval_cases n <;> norm_num at hd

theorem theoremC_models_of_large_sylow_exponent_eight
    (P : Sylow 2 G) (hlo : 32 ≤ Nat.card P) (hhi : Nat.card P ≤ 128)
    (hexp : ∀ x : P, x ^ 8 = 1) (x : P) (hx : orderOf x = 8)
    (hm : IsTheoremCModel G) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ (ClassicalGroup.IsPSL G 3 p ∨ ClassicalGroup.IsPSU G 3 p)) ∨
      Nonempty (G ≃* Sporadic.Mathieu.M12) ∨ Nonempty (G ≃* Sporadic.Mathieu.M22) ∨
      Nonempty (G ≃* Sporadic.Mathieu.M23) ∨ Nonempty (G ≃* Sporadic.LeechRelated.J2.Carrier) := by
  cases hm with
  | alternating n hn hm => exact (no_alternating_le_eight_of_large_sylow_order_eight P hlo x hx hn hm).elim
  | odd hm =>
    cases hm with
    | linear_three p hp ho hm => exact .inl ⟨p,hp,ho,.inl hm⟩
    | unitary_three p hp ho hm => exact .inl ⟨p,hp,ho,.inr hm⟩
    | linear_two p f hp ho _ hm =>
      have hf : 0 < f := by
        obtain ⟨F,_,_,hc,_⟩ := hm
        have hh : 1 < Nat.card F := Finite.one_lt_card
        by_contra hhf
        have he : f=0 := by omega
        simp only [he,pow_zero] at hc
        omega
      exact (not_odd_psl2_of_large_sylow_exponent_eight P hlo hexp
        ⟨p,f,hp,ho,hf,rfl⟩ hm).elim
  | bender hm => exact (no_bender_of_sylow_order_eight P x hx hm).elim
  | rank_two f hm => exact .inl ⟨3,by decide,by decide,
      .inr (unitary_three_of_rankTwo_small_sylow_order_eight P hlo hhi x hx hm)⟩
  | linear_binary n hn hm => exact (no_binary_four_five_of_small_sylow_order_eight P hhi x hx hn hm).elim
  | sporadic hm => exact .inr (sporadic_of_sylow_between_thirty_two_and_128 P hlo hhi hm)

theorem theoremC_degree_three_or_mathieu_of_sylow64
    (P : Sylow 2 G) (hP : Nat.card P = 64)
    (hexp : ∀ x : P, x ^ 8 = 1) (x : P) (hx : orderOf x = 8)
    (hm : IsTheoremCModel G) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ (ClassicalGroup.IsPSL G 3 p ∨ ClassicalGroup.IsPSU G 3 p)) ∨
      Nonempty (G ≃* Sporadic.Mathieu.M12) := by
  have hn128 : ¬128 ∣ Nat.card G := by
    intro hd
    have hh := P.pow_dvd_card_of_pow_dvd_card (n := 7) hd
    rw [hP] at hh
    norm_num at hh
  rcases theoremC_models_of_large_sylow_exponent_eight P (by omega) (by omega) hexp x hx hm with
    hd | h12 | h22 | h23 | hj2
  · exact .inl hd
  · exact .inr h12
  · obtain ⟨e⟩ := h22
    apply (hn128 _).elim
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order]
    norm_num
  · obtain ⟨e⟩ := h23
    apply (hn128 _).elim
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m23_order]
    norm_num
  · obtain ⟨e⟩ := hj2
    apply (hn128 _).elim
    rw [Nat.card_congr e.toEquiv,Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    norm_num
end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.LargeGoldschmidt
