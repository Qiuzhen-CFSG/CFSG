module

public import Theory.Alternating.Aut
public import Theory.SpecificGroups.Alternating.FourPairCore
public import Theory.GroupAction.RegularWreathFunctionModule

/-!
# Automorphisms of a pair of alternating four-groups

We construct the actual automorphism equivalence in Aschbacher--Smith,
Lemma 15.3.9. First Aut(A4) is identified with S4 using the characteristic
Klein four subgroup and a finite generation certificate. A finite normal
subgroup certificate then forces an automorphism of A4 x A4 to preserve or
swap the two factors. Transporting the resulting action through the literal
regular wreath action gives the stated equivalence.
-/

@[expose] public section
open Subgroup
namespace AlternatingFourPair

abbrev K := alternatingGroup.kleinFour (Fin 4)
instance decEqA : DecidableEq A := fun x y => decidable_of_iff (x.1 = y.1) Subtype.coe_injective.eq_iff
abbrev M := A × A
instance decPredK : DecidablePred (fun x : A => x ∈ K) := by
  intro x
  exact decidable_of_iff (x = 1 ∨ (x : Equiv.Perm (Fin 4)).cycleType = {2, 2}) (by
    change _ ↔ x ∈ K
    rw [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four (by norm_num)]
    simp)

theorem klein_generated_by_conjugates (x : A) : x ≠ 1 →
    ∀ v : K, ∃ g h : A, (v : A) = (g * x * g⁻¹) * (h * x⁻¹ * h⁻¹) := by
  fin_cases x <;> decide +kernel

theorem coset_generation (x : A) : x ∉ K →
    ∀ y : A, ∃ v : K, ∃ n : Fin 3, (v : A) * x ^ (n : ℕ) = y := by
  fin_cases x <;> decide +kernel

theorem normalA4 (N : Subgroup A) [hN : N.Normal] :
    N = ⊥ ∨ N = K ∨ N = ⊤ := by
  rcases N.bot_or_exists_ne_one with h | ⟨x, hx, hxne⟩
  · exact Or.inl h
  have hK : K ≤ N := by
    intro v hv
    obtain ⟨g, h, hgh⟩ := klein_generated_by_conjugates x hxne ⟨v, hv⟩
    change (↑(⟨v, hv⟩ : K) : A) ∈ N
    rw [hgh]
    exact N.mul_mem (hN.conj_mem x hx g) (hN.conj_mem x⁻¹ (N.inv_mem hx) h)
  by_cases hNK : N ≤ K
  · exact Or.inr (Or.inl (le_antisymm hNK hK))
  · right; right
    apply top_unique
    intro y hy
    obtain ⟨x, hx, hxK⟩ := SetLike.not_le_iff_exists.mp hNK
    obtain ⟨v, n, rfl⟩ := coset_generation x hxK y
    exact N.mul_mem (hK v.property) (N.pow_mem hx _)


def axis0 : Subgroup M := (⊤ : Subgroup A).prod (⊥ : Subgroup A)
def axis1 : Subgroup M := (⊥ : Subgroup A).prod (⊤ : Subgroup A)
theorem axis0_normal : (axis0 : Subgroup M).Normal := by
  constructor
  intro n hn g
  change g.1 * n.1 * g.1⁻¹ ∈ (⊤ : Subgroup A) ∧ g.2 * n.2 * g.2⁻¹ ∈ (⊥ : Subgroup A)
  simp only [Subgroup.mem_top, Subgroup.mem_bot] at hn ⊢
  constructor
  · simp
  · rw [hn.2]
    simp
theorem axis1_normal : (axis1 : Subgroup M).Normal := by
  constructor
  intro n hn g
  change g.1 * n.1 * g.1⁻¹ ∈ (⊥ : Subgroup A) ∧ g.2 * n.2 * g.2⁻¹ ∈ (⊤ : Subgroup A)
  simp only [Subgroup.mem_top, Subgroup.mem_bot] at hn ⊢
  constructor
  · rw [hn.1]; simp
  · simp
def a (f : MulAut M) : A →* A :=
  (MonoidHom.fst A A).comp (f.toMonoidHom.comp (MonoidHom.inl A A))
def b (f : MulAut M) : A →* A :=
  (MonoidHom.snd A A).comp (f.toMonoidHom.comp (MonoidHom.inl A A))
theorem range_a_normal (f : MulAut M) : (a f).range.Normal := by
  have hmap : (Subgroup.map f.toMonoidHom axis0).Normal :=
    axis0_normal.map f.toMonoidHom f.surjective
  have hinl : (MonoidHom.inl A A).range = axis0 := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      change (x, 1) ∈ (⊤ : Subgroup A).prod (⊥ : Subgroup A)
      exact ⟨by simp, by simp⟩
    · intro hz
      change z.1 ∈ (⊤ : Subgroup A) ∧ z.2 ∈ (⊥ : Subgroup A) at hz
      have hz2 : z.2 = 1 := by simpa using hz.2
      refine ⟨z.1, ?_⟩
      ext <;> simp [hz2]
  have hm : (a f).range = Subgroup.map (MonoidHom.fst A A) (Subgroup.map f.toMonoidHom axis0) := by
    rw [a, MonoidHom.range_comp, MonoidHom.range_comp, hinl]
  rw [hm]
  exact hmap.map (MonoidHom.fst A A) Prod.fst_surjective
theorem range_b_normal (f : MulAut M) : (b f).range.Normal := by
  have hmap : (Subgroup.map f.toMonoidHom axis0).Normal :=
    axis0_normal.map f.toMonoidHom f.surjective
  have hinl : (MonoidHom.inl A A).range = axis0 := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      change (x, 1) ∈ (⊤ : Subgroup A).prod (⊥ : Subgroup A)
      exact ⟨by simp, by simp⟩
    · intro hz
      change z.1 ∈ (⊤ : Subgroup A) ∧ z.2 ∈ (⊥ : Subgroup A) at hz
      have hz2 : z.2 = 1 := by simpa using hz.2
      refine ⟨z.1, ?_⟩
      ext <;> simp [hz2]
  have hm : (b f).range = Subgroup.map (MonoidHom.snd A A) (Subgroup.map f.toMonoidHom axis0) := by
    rw [b, MonoidHom.range_comp, MonoidHom.range_comp, hinl]
  rw [hm]
  exact hmap.map (MonoidHom.snd A A) Prod.snd_surjective


def c (f : MulAut M) : A →* A :=
  (MonoidHom.fst A A).comp (f.toMonoidHom.comp (MonoidHom.inr A A))
def d (f : MulAut M) : A →* A :=
  (MonoidHom.snd A A).comp (f.toMonoidHom.comp (MonoidHom.inr A A))
theorem cross_comm (f : MulAut M) (x y : A) :
    (a f x) * (c f y) = (c f y) * (a f x) ∧
    (b f x) * (d f y) = (d f y) * (b f x) := by
  have h0 : Commute (x, (1 : A)) ((1 : A), y) :=
    Commute.prod (Commute.one_right x) (Commute.one_left y)
  have h := h0.map f
  constructor
  · exact congrArg Prod.fst h.eq
  · exact congrArg Prod.snd h.eq
theorem center_trivial {z : A} (hz : z ∈ Subgroup.center A) : z = 1 := by
  rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 4))] at hz
  exact hz


theorem axis0_card : Nat.card axis0 = 12 := by
  rw [show axis0 = (⊤ : Subgroup A).prod (⊥ : Subgroup A) by rfl]
  rw [Nat.card_congr (Subgroup.prodEquiv (⊤ : Subgroup A) (⊥ : Subgroup A)).toEquiv,
    Nat.card_prod, Subgroup.card_top, Subgroup.card_bot]
  rw [mul_one]
  exact alternatingGroup.card_of_card_eq_four (by norm_num)
theorem map_axis0_card (f : MulAut M) : Nat.card (Subgroup.map f.toMonoidHom axis0) = 12 := by
  have hc := Nat.card_congr (f.subgroupMap axis0).toEquiv
  rw [axis0_card] at hc
  exact hc.symm


theorem comm_le_ker (h : A →* K) : K ≤ h.ker := by
  have hcomm : IsMulCommutative K :=
    (alternatingGroup.kleinFour_isKleinFour (by norm_num : Nat.card (Fin 4) = 4)).isMulCommutative
  have hmap : Subgroup.map h K = ⊥ := by
    have heq : K = commutator A := alternatingGroup.kleinFour_eq_commutator (by norm_num : Nat.card (Fin 4) = 4)
    calc
      Subgroup.map h K = Subgroup.map h (commutator A) := congrArg (fun H : Subgroup A => Subgroup.map h H) heq
      _ = ⁅h.range, h.range⁆ := map_commutator_eq A h
      _ = ⊥ := by
        apply le_antisymm
        · exact (Subgroup.commutator_mono (G := K) le_top le_top).trans_eq (by
            rw [← _root_.commutator_def K, @commutator_eq_bot K _ hcomm])
        · exact bot_le
  intro x hx
  have hx' : h x ∈ Subgroup.map h K := ⟨x, hx, rfl⟩
  rw [hmap] at hx'
  exact hx'

theorem nohom (h : A →* K) : h.range = ⊥ := by
  have hle : K ≤ h.ker := comm_le_ker h
  have hcardK : Nat.card K = 4 := alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)
  have hcardA : Nat.card A = 12 := alternatingGroup.card_of_card_eq_four (by norm_num)
  have hdvd : 4 ∣ Nat.card h.ker := by
    have hh := Subgroup.card_dvd_of_le hle
    have hcardK' : Fintype.card K = 4 := by simpa [Nat.card_eq_fintype_card] using hcardK
    simpa [hcardK'] using hh
  have hmul : Nat.card h.ker * Nat.card h.range = 12 := by
    have hh := h.ker.card_mul_index
    rw [Subgroup.index_ker] at hh
    rw [hcardA] at hh
    exact hh
  have hrdvd : Nat.card h.range ∣ 4 := by
    have hh := Subgroup.card_dvd_of_le (show h.range ≤ (⊤ : Subgroup K) from le_top)
    have hcardK' : Fintype.card K = 4 := by simpa [Nat.card_eq_fintype_card] using hcardK
    simpa [hcardK'] using hh
  have hrle : Nat.card h.range ≤ 4 := Nat.le_of_dvd (by norm_num) hrdvd
  have hr : Nat.card h.range = 1 := by
    obtain ⟨k, hk⟩ := hdvd
    interval_cases hR : Nat.card h.range <;> omega
  exact Subgroup.card_eq_one.mp hr

theorem range_c_normal (f : MulAut M) : (c f).range.Normal := by
  have hmap : (Subgroup.map f.toMonoidHom axis1).Normal :=
    axis1_normal.map f.toMonoidHom f.surjective
  have hinr : (MonoidHom.inr A A).range = axis1 := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      change (1, x) ∈ (⊥ : Subgroup A).prod (⊤ : Subgroup A)
      exact ⟨by simp, by simp⟩
    · intro hz
      change z.1 ∈ (⊥ : Subgroup A) ∧ z.2 ∈ (⊤ : Subgroup A) at hz
      have hz1 : z.1 = 1 := by simpa using hz.1
      refine ⟨z.2, ?_⟩
      ext <;> simp [hz1]
  have hm : (c f).range = Subgroup.map (MonoidHom.fst A A) (Subgroup.map f.toMonoidHom axis1) := by
    rw [c, MonoidHom.range_comp, MonoidHom.range_comp, hinr]
  rw [hm]
  exact hmap.map (MonoidHom.fst A A) Prod.fst_surjective
theorem range_d_normal (f : MulAut M) : (d f).range.Normal := by
  have hmap : (Subgroup.map f.toMonoidHom axis1).Normal :=
    axis1_normal.map f.toMonoidHom f.surjective
  have hinr : (MonoidHom.inr A A).range = axis1 := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      change (1, x) ∈ (⊥ : Subgroup A).prod (⊤ : Subgroup A)
      exact ⟨by simp, by simp⟩
    · intro hz
      change z.1 ∈ (⊥ : Subgroup A) ∧ z.2 ∈ (⊤ : Subgroup A) at hz
      have hz1 : z.1 = 1 := by simpa using hz.1
      refine ⟨z.2, ?_⟩
      ext <;> simp [hz1]
  have hm : (d f).range = Subgroup.map (MonoidHom.snd A A) (Subgroup.map f.toMonoidHom axis1) := by
    rw [d, MonoidHom.range_comp, MonoidHom.range_comp, hinr]
  rw [hm]
  exact hmap.map (MonoidHom.snd A A) Prod.snd_surjective
theorem factor_range_cases (f : MulAut M) :
    (a f).range = ⊥ ∨ (a f).range = K ∨ (a f).range = ⊤ := by
  exact @normalA4 (a f).range (range_a_normal f)
theorem factor_range_cases_b (f : MulAut M) :
    (b f).range = ⊥ ∨ (b f).range = K ∨ (b f).range = ⊤ := by
  exact @normalA4 (b f).range (range_b_normal f)
theorem factor_range_cases_c (f : MulAut M) :
    (c f).range = ⊥ ∨ (c f).range = K ∨ (c f).range = ⊤ := by
  exact @normalA4 (c f).range (range_c_normal f)
theorem factor_range_cases_d (f : MulAut M) :
    (d f).range = ⊥ ∨ (d f).range = K ∨ (d f).range = ⊤ := by
  exact @normalA4 (d f).range (range_d_normal f)

theorem hom_one_of_surjective_commute (u v : A →* A)
    (hcomm : ∀ x y, u x * v y = v y * u x)
    (hv : Function.Surjective v) : u = 1 := by
  apply MonoidHom.ext
  intro x
  have hz : u x ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := hv z
    exact (hcomm x y).symm
  exact center_trivial hz

theorem other_injective_of_one (f : MulAut M) (hb : b f = 1) :
    Function.Injective (a f) := by
  intro x y hxy
  have hf : f (x, 1) = f (y, 1) := by
    apply Prod.ext
    · change a f x = a f y
      exact hxy
    · change b f x = b f y
      rw [hb]
      simp
  exact congrArg Prod.fst (f.injective hf)

theorem other_injective_of_one' (f : MulAut M) (ha : a f = 1) :
    Function.Injective (b f) := by
  intro x y hxy
  have hf : f (x, 1) = f (y, 1) := by
    apply Prod.ext
    · change a f x = a f y
      rw [ha]
      simp
    · change b f x = b f y
      exact hxy
  exact congrArg Prod.fst (f.injective hf)

theorem axis0_le_KK (f : MulAut M)
    (ha : (a f).range = K) (hb : (b f).range = K) :
    Subgroup.map f.toMonoidHom axis0 ≤ K.prod K := by
  rintro z ⟨x, hx, rfl⟩
  change f (x : M) ∈ K.prod K
  rcases x with ⟨x, y⟩
  have hx' : x ∈ (⊤ : Subgroup A) ∧ y ∈ (⊥ : Subgroup A) := by
    change x ∈ (⊤ : Subgroup A) ∧ y ∈ (⊥ : Subgroup A) at hx
    exact hx
  have hy : y = 1 := by simpa using hx'.2
  subst y
  have hax : a f x ∈ K := by rw [← ha]; exact ⟨x, rfl⟩
  have hbx : b f x ∈ K := by rw [← hb]; exact ⟨x, rfl⟩
  change (a f x, b f x) ∈ K.prod K
  exact ⟨hax, hbx⟩

theorem K_ne_bot : K ≠ (⊥ : Subgroup A) := by
  intro h
  have hc := congrArg (fun H : Subgroup A => Nat.card H) h
  rw [alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num), Subgroup.card_bot] at hc
  norm_num at hc
theorem K_ne_top : K ≠ (⊤ : Subgroup A) := by
  intro h
  have hc := congrArg (fun H : Subgroup A => Nat.card H) h
  rw [alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num), Subgroup.card_top]
    at hc
  have hA := alternatingGroup.card_of_card_eq_four (by norm_num : Nat.card (Fin 4) = 4)
  rw [hA] at hc
  norm_num at hc

theorem factor_choice (f : MulAut M) :
    ((a f).range = ⊥ ∧ (b f).range = ⊤ ∧
      (c f).range = ⊤ ∧ (d f).range = ⊥) ∨
    ((a f).range = ⊤ ∧ (b f).range = ⊥ ∧
      (c f).range = ⊥ ∧ (d f).range = ⊤) := by
  rcases factor_range_cases f with ha0 | haK | haT
  · have ha1 : a f = 1 := MonoidHom.range_eq_bot_iff.mp ha0
    have hbi : Function.Injective (b f) := other_injective_of_one' f ha1
    have hbs : Function.Surjective (b f) := (Function.Injective.bijective_of_finite hbi).2
    have hbT : (b f).range = ⊤ := MonoidHom.range_eq_top.mpr hbs
    have hd1 : d f = 1 := by
      apply hom_one_of_surjective_commute (d f) (b f)
        (fun y x => (cross_comm f x y).2.symm)
        hbs
    have hci : Function.Injective (c f) := by
      intro x y hxy
      have hf : f (1, x) = f (1, y) := by
        apply Prod.ext
        · change c f x = c f y
          exact hxy
        · change d f x = d f y
          rw [hd1]
          simp
      exact congrArg Prod.snd (f.injective hf)
    have hcs : Function.Surjective (c f) :=
      (Function.Injective.bijective_of_finite hci).2
    have hcT : (c f).range = ⊤ := MonoidHom.range_eq_top.mpr hcs
    exact Or.inl ⟨ha0, hbT, hcT, MonoidHom.range_eq_bot_iff.mpr hd1⟩
  · rcases factor_range_cases_b f with hb0 | hbK | hbT
    · have hb1 : b f = 1 := MonoidHom.range_eq_bot_iff.mp hb0
      have hai : Function.Injective (a f) := other_injective_of_one f hb1
      have has : Function.Surjective (a f) := (Function.Injective.bijective_of_finite hai).2
      have haT : (a f).range = ⊤ := MonoidHom.range_eq_top.mpr has
      exact False.elim (K_ne_top (haK.symm.trans haT))
    · have hle := axis0_le_KK f haK hbK
      have hcard := Subgroup.card_dvd_of_le hle
      have hmapcard := map_axis0_card f
      have hprodcard : Nat.card (K.prod K) = 16 := by
        rw [Nat.card_congr (Subgroup.prodEquiv K K).toEquiv, Nat.card_prod]
        rw [alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)]
      rw [hmapcard, hprodcard] at hcard
      norm_num at hcard
    · have hbs : Function.Surjective (b f) := MonoidHom.range_eq_top.mp hbT
      have hd1 : d f = 1 := by
        apply hom_one_of_surjective_commute (d f) (b f)
          (fun y x => (cross_comm f x y).2.symm)
          hbs
      have hci : Function.Injective (c f) := by
        intro x y hxy
        have hf : f (1, x) = f (1, y) := by
          apply Prod.ext
          · change c f x = c f y
            exact hxy
          · change d f x = d f y
            rw [hd1]
            simp
        exact congrArg Prod.snd (f.injective hf)
      have hcs : Function.Surjective (c f) :=
        (Function.Injective.bijective_of_finite hci).2
      have hac : a f = 1 := by
        apply hom_one_of_surjective_commute (a f) (c f)
          (fun x y => (cross_comm f x y).1)
          hcs
      have hac0 : (a f).range = ⊥ := MonoidHom.range_eq_bot_iff.mpr hac
      exact False.elim (K_ne_bot (haK.symm.trans hac0))
  · have has : Function.Surjective (a f) := MonoidHom.range_eq_top.mp haT
    have hc1 : c f = 1 := by
      apply hom_one_of_surjective_commute (c f) (a f)
        (fun y x => (cross_comm f x y).1.symm)
        has
    have hdi : Function.Injective (d f) := by
      intro x y hxy
      have hf : f (1, x) = f (1, y) := by
        apply Prod.ext
        · change c f x = c f y
          rw [hc1]
          simp
        · change d f x = d f y
          exact hxy
      exact congrArg Prod.snd (f.injective hf)
    have hds : Function.Surjective (d f) := (Function.Injective.bijective_of_finite hdi).2
    have hb1 : b f = 1 := by
      apply hom_one_of_surjective_commute (b f) (d f)
        (fun x y => (cross_comm f x y).2)
        hds
    have hb0 : (b f).range = ⊥ := MonoidHom.range_eq_bot_iff.mpr hb1
    exact Or.inr ⟨haT, hb0, MonoidHom.range_eq_bot_iff.mpr hc1,
      MonoidHom.range_eq_top.mpr hds⟩

abbrev D := Equiv.Perm (Fin 4)
abbrev Q := Multiplicative (ZMod 2)
abbrev W := RegularWreathProduct D Q
instance fintypeS : Fintype {p : Equiv.Perm K // p 1 = 1} := inferInstance
abbrev S := {p : Equiv.Perm K // p 1 = 1}
abbrev C := {x : A // x ^ 3 = 1 ∧ x ≠ 1}

def c3 : A := ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel⟩
theorem c_cube : c3 ^ 3 = 1 := by
  apply Subtype.ext
  decide +kernel
theorem c_order_ne : c3 ≠ 1 := by
  intro h
  have hn : (Equiv.swap 1 2 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) ≠ 1 := by decide +kernel
  exact hn (congrArg Subtype.val h)
theorem c_order : orderOf c3 = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    decide +kernel
  · intro h
    exact c_order_ne h

def restrictK (φ : MulAut A) : MulAut K where
  toFun v := ⟨φ v, by
    have hm := (Subgroup.characteristic_iff_map_eq.mp
      (alternatingGroup.characteristic_kleinFour (by norm_num : Nat.card (Fin 4) = 4))) φ
    have hv : φ (v : A) ∈ Subgroup.map φ.toMonoidHom K := ⟨v, v.property, rfl⟩
    rw [hm] at hv
    exact hv⟩
  invFun v := ⟨φ.symm v, by
    have hm := (Subgroup.characteristic_iff_map_eq.mp
      (alternatingGroup.characteristic_kleinFour (by norm_num : Nat.card (Fin 4) = 4))) φ.symm
    have hv : φ.symm (v : A) ∈ Subgroup.map φ.symm.toMonoidHom K := ⟨v, v.property, rfl⟩
    rw [hm] at hv
    exact hv⟩
  left_inv v := by simp
  right_inv v := by simp
  map_mul' x y := by simp

theorem restrictK_one (φ : MulAut A) : (restrictK φ) 1 = 1 := by simp

def T := {z : S × C // ∀ v : K,
    (z.1.1 ⟨c3 * v * c3⁻¹, by
      have hn := alternatingGroup.normal_kleinFour (by norm_num : Nat.card (Fin 4) = 4)
      exact hn.conj_mem (v : A) v.property c3⟩) =
      ⟨(z.2 : A) * z.1.1 v * (z.2 : A)⁻¹, by
        have hn := alternatingGroup.normal_kleinFour (by norm_num : Nat.card (Fin 4) = 4)
        exact hn.conj_mem (z.1.1 v : A) (z.1.1 v).property (z.2 : A)⟩}

instance fintypeT : Fintype T := by
  unfold T
  infer_instance

def encode (φ : MulAut A) : T := by
  let r : S := ⟨(restrictK φ).toEquiv, restrictK_one φ⟩
  let y : C := ⟨φ c3, by
    constructor
    · rw [← map_pow, c_cube]
      simp
    · intro h; apply c_order_ne; rw [← φ.injective.eq_iff]; simpa using h⟩
  refine ⟨(r,y), ?_⟩
  intro v
  apply Subtype.ext
  change φ (c3 * (v : A) * c3⁻¹) = φ c3 * φ (v : A) * (φ c3)⁻¹
  rw [map_mul, map_mul]; simp

theorem genA : ∀ x : A, ∃ v : K, ∃ n : Fin 3, (v : A) * c3 ^ (n : ℕ) = x := by
  decide +kernel

theorem encode_injective : Function.Injective encode := by
  intro φ ψ h
  apply MulEquiv.ext
  intro x
  obtain ⟨v, n, rfl⟩ := genA x
  have hv : (restrictK φ v : A) = (restrictK ψ v : A) := by
    have hh := congrArg (fun z : T => z.1.1.1 v) h
    exact congrArg Subtype.val hh
  have hc : φ c3 = ψ c3 := by
    have hh := congrArg (fun z : T => (z.1.2 : A)) h
    exact hh
  have hv' : φ (v : A) = ψ (v : A) := by simpa [restrictK] using hv
  simp only [map_mul, map_pow, hv', hc]

theorem cardT : Fintype.card T = 24 := by decide +kernel
def conjA : Equiv.Perm (Fin 4) →* MulAut A :=
  MulAut.conjNormal (H := A) 
theorem conjA_inj : Function.Injective conjA :=
  GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 4 (by norm_num)
theorem card_aut_le : Nat.card (MulAut A) ≤ Nat.card (Equiv.Perm (Fin 4)) := by
  calc
    Nat.card (MulAut A) ≤ Nat.card T := Nat.card_le_card_of_injective encode encode_injective
    _ = Fintype.card T := Nat.card_eq_fintype_card
    _ = 24 := by rw [cardT]
    _ = Nat.card (Equiv.Perm (Fin 4)) := by
      rw [Nat.card_perm]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]
theorem conjA_bij : Function.Bijective conjA :=
  conjA_inj.bijective_of_nat_card_le (by
    simpa [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial] using card_aut_le)
noncomputable def eA : D ≃* MulAut A := MulEquiv.ofBijective conjA conjA_bij
noncomputable def pairFunction : M ≃* (Q → A) where
  toFun v i := if i = 1 then v.1 else v.2
  invFun v := (v 1, v (Multiplicative.ofAdd 1))
  left_inv v := by simp
  right_inv v := by
    funext i
    have hi : ∀i : Q, i = 1 ∨ i = Multiplicative.ofAdd 1 := by decide
    rcases hi i with rfl | rfl <;> simp [show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 from by decide]
  map_mul' v w := by
    funext i
    by_cases hi : i = 1 <;> simp [hi]

noncomputable def wreathAut : W →* MulAut M := by
  letI : MulDistribMulAction D A := MulDistribMulAction.compHom A eA.toMonoidHom
  letI : FaithfulSMul D A := by
    constructor
    intro a b h
    apply eA.injective
    apply MulEquiv.ext
    intro x
    exact h x
  letI : Nontrivial A := by infer_instance
  letI := RegularWreathProduct.functionModule D Q A
  exact (MulAut.congr pairFunction).symm.toMonoidHom.comp
    (MulDistribMulAction.toMulAut W (Q → A))
set_option linter.style.haveILetI false in
theorem wreathAut_injective : Function.Injective wreathAut := by
  intro w z h
  letI : MulDistribMulAction D A := MulDistribMulAction.compHom A eA.toMonoidHom
  letI : FaithfulSMul D A := by
    constructor
    intro a b hab
    apply eA.injective
    apply MulEquiv.ext
    intro x
    exact hab x
  letI : Nontrivial A := by infer_instance
  letI := RegularWreathProduct.functionModule D Q A
  letI : FaithfulSMul W (Q → A) := by
    exact RegularWreathProduct.functionModule_faithful D Q A
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Q → A)
  intro v
  obtain ⟨v, rfl⟩ := pairFunction.surjective v
  have hh := congrArg (fun e : MulAut M => pairFunction (e v)) h
  simpa [wreathAut, MulAut.congr] using hh

theorem right_injective_of_one (f : MulAut M) (hc : c f = 1) :
    Function.Injective (d f) := by
  intro x y hxy
  have hf : f (1, x) = f (1, y) := by
    apply Prod.ext
    · change c f x = c f y
      rw [hc]
      simp
    · change d f x = d f y
      exact hxy
  exact congrArg Prod.snd (f.injective hf)

theorem right_injective_of_one' (f : MulAut M) (hd : d f = 1) :
    Function.Injective (c f) := by
  intro x y hxy
  have hf : f (1, x) = f (1, y) := by
    apply Prod.ext
    · change c f x = c f y
      exact hxy
    · change d f x = d f y
      rw [hd]
      simp
  exact congrArg Prod.snd (f.injective hf)

theorem factor_formula (f : MulAut M) :
    (∃ α β : MulAut A, ∀v, f v = (α v.1, β v.2)) ∨
    (∃ α β : MulAut A, ∀v, f v = (α v.2, β v.1)) := by
  rcases factor_choice f with hs | hp
  · obtain ⟨ha0, hbT, hcT, hd0⟩ := hs
    have ha1 : a f = 1 := MonoidHom.range_eq_bot_iff.mp ha0
    have hd1 : d f = 1 := MonoidHom.range_eq_bot_iff.mp hd0
    have hbi : Function.Injective (b f) := other_injective_of_one' f ha1
    have hci : Function.Injective (c f) := right_injective_of_one' f hd1
    have hbs : Function.Surjective (b f) := (Function.Injective.bijective_of_finite hbi).2
    have hcs : Function.Surjective (c f) := (Function.Injective.bijective_of_finite hci).2
    let α : MulAut A := MulEquiv.ofBijective (c f) ⟨hci, hcs⟩
    let β : MulAut A := MulEquiv.ofBijective (b f) ⟨hbi, hbs⟩
    right
    refine ⟨α, β, ?_⟩
    intro v
    have hv : v = (v.1, 1) * (1, v.2) := by ext <;> simp
    rw [hv, map_mul]
    have hleft : f (v.1, 1) = (1, b f v.1) := by
      apply Prod.ext
      · change a f v.1 = 1
        rw [ha1]
        simp
      · rfl
    have hright : f (1, v.2) = (c f v.2, 1) := by
      apply Prod.ext
      · rfl
      · change d f v.2 = 1
        rw [hd1]
        simp
    rw [hleft, hright]
    rfl
  · obtain ⟨haT, hb0, hc0, hdT⟩ := hp
    have hb1 : b f = 1 := MonoidHom.range_eq_bot_iff.mp hb0
    have hc1 : c f = 1 := MonoidHom.range_eq_bot_iff.mp hc0
    have hai : Function.Injective (a f) := other_injective_of_one f hb1
    have hdi : Function.Injective (d f) := right_injective_of_one f hc1
    have has : Function.Surjective (a f) := (Function.Injective.bijective_of_finite hai).2
    have hds : Function.Surjective (d f) := (Function.Injective.bijective_of_finite hdi).2
    let α : MulAut A := MulEquiv.ofBijective (a f) ⟨hai, has⟩
    let β : MulAut A := MulEquiv.ofBijective (d f) ⟨hdi, hds⟩
    left
    refine ⟨α, β, ?_⟩
    intro v
    have hv : v = (v.1, 1) * (1, v.2) := by ext <;> simp
    rw [hv, map_mul]
    have hleft : f (v.1, 1) = (a f v.1, 1) := by
      apply Prod.ext
      · rfl
      · change b f v.1 = 1
        rw [hb1]
        simp
    have hright : f (1, v.2) = (1, d f v.2) := by
      apply Prod.ext
      · change c f v.2 = 1
        rw [hc1]
        simp
      · rfl
    rw [hleft, hright]
    rfl

set_option linter.style.haveILetI false in
theorem wreathAut_pair (w : W) (v : M) (i : Q) :
    pairFunction (wreathAut w v) i = eA (w.left i) (pairFunction v (w.right⁻¹ * i)) := by
  letI : MulDistribMulAction D A := MulDistribMulAction.compHom A eA.toMonoidHom
  letI : FaithfulSMul D A := by
    constructor
    intro a b hab
    apply eA.injective
    apply MulEquiv.ext
    intro x
    exact hab x
  letI : Nontrivial A := by infer_instance
  letI := RegularWreathProduct.functionModule D Q A
  simp [wreathAut, MulAut.congr, RegularWreathProduct.functionModule_smul_apply]
  change eA (w.left i) (pairFunction v (w.right⁻¹ * i)) = _
  rfl

theorem exists_wreath_formula (f : MulAut M) :
    ∃w : W, ∀v, wreathAut w v = f v := by
  rcases factor_formula f with ⟨α, β, h⟩ | ⟨α, β, h⟩
  · let w : W := ⟨(fun i => if i = 1 then eA.symm α else eA.symm β), 1⟩
    refine ⟨w, ?_⟩
    intro v
    apply pairFunction.injective
    funext i
    have hi : ∀j : Q, j = 1 ∨ j = Multiplicative.ofAdd 1 := by decide
    rcases hi i with rfl | rfl
    · rw [wreathAut_pair]
      simp [w, pairFunction, h]
    · rw [wreathAut_pair]
      simp [w, pairFunction, h]
  · let w : W := ⟨(fun i => if i = 1 then eA.symm α else eA.symm β), Multiplicative.ofAdd 1⟩
    refine ⟨w, ?_⟩
    intro v
    apply pairFunction.injective
    funext i
    have hi : ∀j : Q, j = 1 ∨ j = Multiplicative.ofAdd 1 := by decide
    have ht : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
    have htinv : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by decide
    have htt : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
    rcases hi i with rfl | rfl
    · rw [wreathAut_pair]
      simp [w, pairFunction, h, ht, htinv]
    · rw [wreathAut_pair]
      simp [w, pairFunction, h, ht, htinv, htt]

noncomputable def chooseW (f : MulAut M) : W :=
  Classical.choose (exists_wreath_formula f)
theorem chooseW_spec (f : MulAut M) :
    ∀v, wreathAut (chooseW f) v = f v := Classical.choose_spec (exists_wreath_formula f)
theorem chooseW_injective : Function.Injective chooseW := by
  intro f g h
  apply MulEquiv.ext
  intro v
  rw [← chooseW_spec f v, ← chooseW_spec g v, h]

theorem card_aut_pair_le : Nat.card (MulAut M) ≤ Nat.card W := by
  exact Nat.card_le_card_of_injective chooseW chooseW_injective

theorem wreathAut_bij : Function.Bijective wreathAut :=
  wreathAut_injective.bijective_of_nat_card_le card_aut_pair_le

noncomputable def pairAutEquiv : W ≃* MulAut M :=
  MulEquiv.ofBijective wreathAut wreathAut_bij

noncomputable def pairAutEquiv' : MulAut M ≃* W := pairAutEquiv.symm

/-- The full automorphism group of the literal pair A4 x A4 is the literal
regular wreath product S4 wreath C2. -/
noncomputable def mulAut_equiv_regularWreath :
    MulAut Model ≃* RegularWreathProduct (Equiv.Perm (Fin 4))
      (Multiplicative (ZMod 2)) := pairAutEquiv'

/-- Alias emphasizing the symmetric-group base of the wreath product. -/
noncomputable def mulAut_equiv_symmetric_wreath :
    MulAut Model ≃* RegularWreathProduct (Equiv.Perm (Fin 4))
      (Multiplicative (ZMod 2)) := mulAut_equiv_regularWreath

end AlternatingFourPair

end
