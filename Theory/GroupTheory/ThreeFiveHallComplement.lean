module

public import Mathlib.GroupTheory.SemidirectProduct
public import Theory.GroupTheory.SolvableFiveNormalizer
public import Mathlib.GroupTheory.Transfer
public import Theory.GroupTheory.PGroup.Omega

/-!
# An actual three-by-five subgroup from a confined five-normalizer

A Sylow five-subgroup of order five in a finite solvable group lies in a
Hall {3,5}-subgroup. If its normalizer has no factor of three, its normalizer
inside this Hall subgroup is itself. Burnside transfer supplies a normal
five-complement, a three-group nontrivial whenever the ambient group has a factor of three.
The first omega subgroup of its center then supplies a nontrivial elementary
three-group and an embedded semidirect product with the original complement.

These are the Hall and transfer steps in Thompson VI, printed p.630.
-/

namespace Subgroup

open scoped IsMulCommutative

/-- Actual Hall and normal-complement witnesses for the three-by-five action. -/
public theorem exists_three_five_hall_normal_complement
    {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    (A : Sylow 5 G) (hA : Nat.card A = 5)
    (hN : ¬ 3 ∣ Nat.card (normalizer (A : Set G)))
    (h3 : 3 ∣ Nat.card G) :
    ∃ (H : Subgroup G) (_hAH : (A : Subgroup G) ≤ H),
      IsHallSubgroup {p : Nat.Primes | p.val = 3 ∨ p.val = 5} H ∧
      ∃ P : Subgroup H, P.Normal ∧ IsPGroup 3 P ∧ P ≠ ⊥ ∧
        P.IsComplement' ((A : Subgroup G).subgroupOf H) ∧
        P ⊓ centralizer (((A : Subgroup G).subgroupOf H) : Set H) = ⊥ := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : MulDistribMulAction Unit G := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  let π : Set Nat.Primes := {p | p.val = 3 ∨ p.val = 5}
  have hAπ : IsPiSubgroup π (A : Subgroup G) := by
    intro p hp
    rw [hA] at hp
    exact Or.inr ((Nat.dvd_prime (by decide)).mp hp |>.resolve_left p.property.ne_one)
  have hinv : IsInvariant Unit G (A : Subgroup G) := ⟨fun _ _ => Iff.rfl⟩
  obtain ⟨H, hHall, _, hAH⟩ := exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (A := Unit) hsolv (by simp) π (A : Subgroup G) hAπ hinv
  let AH := A.subtype hAH
  have hAHcard : Nat.card AH = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).trans hA
  have hNmap : (normalizer (AH : Set H)).map H.subtype ≤ normalizer (A : Set G) := by
    have hh := le_normalizer_map (H := (A : Subgroup G).subgroupOf H) H.subtype
    rwa [map_subgroupOf_eq_of_le hAH] at hh
  have hno3 : ¬ 3 ∣ Nat.card (normalizer (AH : Set H)) := by
    intro h
    apply hN
    have hd := card_dvd_of_le hNmap
    rw [card_map_of_injective H.subtype_injective] at hd
    exact h.trans hd
  have hNfive : IsPGroup 5 (normalizer (AH : Set H)) := by
    apply IsPGroup.of_card
    apply Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos.ne')
    intro p hp hpd
    have hpi := hHall.p_in_pi_of_p_dvd_card ⟨p, hp⟩
      (hpd.trans (normalizer (AH : Set H)).card_subgroup_dvd_card)
    rcases hpi with h | h
    · exact (hno3 (h ▸ hpd)).elim
    · exact h
  have hNeq : normalizer (AH : Set H) = AH :=
    AH.is_maximal' hNfive AH.toSubgroup.le_normalizer
  let _ : IsCyclic AH := isCyclic_of_prime_card hAHcard
  have hNC : normalizer (AH : Set H) ≤ centralizer (AH : Set H) := by
    rw [hNeq]
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨b, hb⟩ : AH) ⟨a, ha⟩)
  let P := (MonoidHom.transferSylow AH hNC).ker
  have hcomp : P.IsComplement' AH := MonoidHom.ker_transferSylow_isComplement' AH hNC
  have hPthree : IsPGroup 3 P := by
    apply IsPGroup.of_card
    apply Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos.ne')
    intro p hp hpd
    have hpi := hHall.p_in_pi_of_p_dvd_card ⟨p, hp⟩
      (hpd.trans P.card_subgroup_dvd_card)
    rcases hpi with h | h
    · exact h
    · have hp5 : p = 5 := h
      subst p
      exact (MonoidHom.not_dvd_card_ker_transferSylow AH hNC hpd).elim
  have h3H : 3 ∣ Nat.card H := by
    have hi3 : ¬ 3 ∣ H.index := fun h =>
      hHall.p_in_pi_of_p_dvd_index ⟨3, by decide⟩ h (Or.inl rfl)
    have hm : 3 ∣ Nat.card H * H.index := H.card_mul_index.symm ▸ h3
    exact ((show Nat.Prime 3 by decide).dvd_mul.mp hm).resolve_right hi3
  have hPne : P ≠ ⊥ := by
    intro h
    have hc := hcomp.card_mul_card
    rw [h, card_bot, one_mul, hAHcard] at hc
    rw [← hc] at h3H
    norm_num at h3H
  refine ⟨H, hAH, hHall, P, inferInstance, hPthree, hPne, hcomp, ?_⟩
  apply bot_unique
  apply le_trans (inf_le_inf_left P (centralizer_le_normalizer _))
  change P ⊓ normalizer (AH : Set H) ≤ ⊥
  rw [hNeq]
  exact hcomp.disjoint.le_bot

/-- The characteristic elementary central layer of the normal five-complement. -/
public theorem exists_normal_elementary_three_of_normal_three
    {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) [P.Normal] (hP : IsPGroup 3 P) (hne : P ≠ ⊥) :
    ∃ B : Subgroup G, B.Normal ∧ IsElementaryAbelian 3 B ∧ B ≠ ⊥ ∧ B ≤ P := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Nontrivial P := P.nontrivial_iff_ne_bot.mpr hne
  let _ : Nontrivial (center P) := hP.center_nontrivial
  let O := omega₁ (center P) (p := 3)
  let _ : O.Characteristic := omega₁_characteristic _
  let _ : IsElementaryAbelian 3 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let B0 := O.map (center P).subtype
  let _ : B0.Characteristic := inferInstance
  let _ : IsElementaryAbelian 3 B0 := IsElementaryAbelian.map_subtype
  let B := B0.map P.subtype
  have hdiv : 3 ∣ Nat.card (center P) := (hP.to_subgroup (center P)).card_eq_or_dvd.resolve_left
    (by have := Finite.one_lt_card (α := center P); omega)
  have hB0 : B0 ≠ ⊥ := omega₁_map_subtype_ne_bot (center P) 3 hdiv
  refine ⟨B, ConjAct.normal_of_characteristic_of_normal,
    IsElementaryAbelian.map_subtype, ?_, map_subtype_le _⟩
  intro hb
  apply hB0
  exact (map_injective (f := P.subtype) P.subtype_injective) (by simpa using hb)

/-- The elementary central layer and the original complement embed as an actual semidirect product. -/
public theorem exists_elementary_three_semidirect_embedding
    {G : Type*} [Group G] [Finite G]
    (P A : Subgroup G) [P.Normal] (hP : IsPGroup 3 P) (hne : P ≠ ⊥)
    (hd : Disjoint P A) (hfix : P ⊓ centralizer (A : Set G) = ⊥) :
    ∃ (B : Subgroup G) (_ : IsElementaryAbelian 3 B), B ≠ ⊥ ∧
      ∃ (φ : A →* MulAut B) (ι : SemidirectProduct B A φ →* G),
        Function.Injective ι ∧
        (∀ b : B, ι (SemidirectProduct.inl b) = b) ∧
        (∀ a : A, ι (SemidirectProduct.inr a) = a) ∧
        (∀ b : B, (∀ a : A, φ a b = b) → b = 1) := by
  obtain ⟨B, hBN, hB3, hBne, hBP⟩ :=
    exists_normal_elementary_three_of_normal_three P hP hne
  let _ : B.Normal := hBN
  have hAB : A ≤ normalizer (B : Set G) := B.normalizer_eq_top ▸ le_top
  let φ := B.normalizerMonoidHom.comp (inclusion hAB)
  let ι : SemidirectProduct B A φ →* G := SemidirectProduct.monoidHomSubgroup hAB
  refine ⟨B, hB3, hBne, φ, ι, ?_, ?_, ?_, ?_⟩
  · apply (MonoidHom.ker_eq_bot_iff ι).mp
    apply bot_unique
    intro x hx
    have heq : (x.left : G) * (x.right : G) = 1 := hx
    have hleft : (x.left : G) = 1 := hd.le_bot ⟨hBP x.left.property,
      (mul_eq_one_iff_eq_inv.mp heq) ▸ A.inv_mem x.right.property⟩
    have hright : (x.right : G) = 1 := by simpa only [hleft, one_mul] using heq
    apply mem_bot.mpr
    apply SemidirectProduct.ext
    · exact Subtype.ext hleft
    · exact Subtype.ext hright
  · intro b
    simp [ι, SemidirectProduct.monoidHomSubgroup]
  · intro a
    simp [ι, SemidirectProduct.monoidHomSubgroup]
  · intro b hb
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hfix]
    refine ⟨hBP b.property, ?_⟩
    intro a ha
    have he := congrArg Subtype.val (hb ⟨a, ha⟩)
    change a * (b : G) * a⁻¹ = b at he
    exact (mul_inv_eq_iff_eq_mul.mp he)

/-- The canonical factors retain all hypotheses for the native three-by-five action theorem. -/
public theorem three_five_semidirect_subgroup_data {B A : Type*} [Group B] [Finite B] [Group A] [Finite A]
    [IsElementaryAbelian 3 B] [Nontrivial B]
    (hA : Nat.card A = 5) (φ : A →* MulAut B)
    (hfree : ∀ b : B, (∀ a : A, φ a b = b) → b = 1) :
    let H := SemidirectProduct B A φ
    let L := (SemidirectProduct.inl : B →* H).range
    let T := (SemidirectProduct.inr : A →* H).range
    L.Normal ∧ IsElementaryAbelian 3 L ∧ L ≠ ⊥ ∧ Nat.card T = 5 ∧
      L.IsComplement' T ∧ L ⊓ centralizer (T : Set H) = ⊥ := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let H := SemidirectProduct B A φ
  let _ : Finite H := Finite.of_equiv (B × A) SemidirectProduct.equivProd.symm
  let L := (SemidirectProduct.inl : B →* H).range
  let T := (SemidirectProduct.inr : A →* H).range
  have hLN : L.Normal := by
    dsimp [L]
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  let e : B ≃* L := MonoidHom.ofInjective SemidirectProduct.inl_injective
  have hL3 : IsElementaryAbelian 3 L := {
    toIsMulCommutative := ⟨⟨fun x y => e.symm.injective (by
      simp only [map_mul]
      exact mul_comm' _ _)⟩⟩
    exponent_dvd_p := by
      rw [← Monoid.exponent_eq_of_mulEquiv e]
      exact IsElementaryAbelian.exponent_dvd_p 3 B }
  have hLcard : Nat.card L = Nat.card B :=
    (Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv).symm
  have hTcard : Nat.card T = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inr_injective).toEquiv).symm
  have hLne : L ≠ ⊥ := by
    intro h
    have hc := Finite.one_lt_card (α := B)
    rw [h, card_bot] at hLcard
    omega
  have hd : Disjoint L T := by
    apply disjoint_def.mpr
    rintro x ⟨b, rfl⟩ ⟨a, ha⟩
    have hb : b = 1 := by
      have hh := congrArg SemidirectProduct.left ha
      simpa using hh.symm
    simp [hb]
  refine ⟨hLN, hL3, hLne, hTcard.trans hA,
    isComplement'_of_card_mul_and_disjoint ?_ hd, ?_⟩
  · rw [hLcard, hTcard, SemidirectProduct.card]
  · apply bot_unique
    rintro x ⟨⟨b, rfl⟩, hc⟩
    have hb : b = 1 := hfree b (by
      intro a
      have he := congrArg SemidirectProduct.left
        (mem_centralizer_iff.mp hc (SemidirectProduct.inr a) ⟨a, rfl⟩)
      simpa using he)
    simp [hb]

end Subgroup
