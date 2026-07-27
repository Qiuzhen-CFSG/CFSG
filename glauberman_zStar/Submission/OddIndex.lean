import Mathlib
open Subgroup
open Finset

noncomputable section
open Classical

namespace Submission.OddIndex

variable {G : Type*} [Group G] [Fintype G] (t : G)

lemma inv_eq_self_of_sq_eq_one (ht2 : t * t = 1) : t⁻¹ = t := by
  apply inv_eq_of_mul_eq_one_left; rw [ht2]

/-- A combinatorial lemma: if an involution f on a Finset s has exactly one fixed point a,
    then s has odd cardinality. -/
lemma card_odd_of_involution_unique_fixed {α : Type*} [DecidableEq α] (s : Finset α) (f : α → α)
    (hfs : ∀ x ∈ s, f x ∈ s) (h_invol : ∀ x, f (f x) = x) (a : α) (ha_mem : a ∈ s) (ha_fixed : f a = a)
    (h_unique : ∀ x ∈ s, f x = x → x = a) : Odd s.card := by
  by_cases h_s_singleton : s = {a}
  · subst h_s_singleton; simp
  · have h_exists : ∃ x ∈ s, x ≠ a := by
      by_contra! h_all_eq
      apply h_s_singleton
      have h_sub : s ⊆ {a} := by
        intro y hy; simp [h_all_eq y hy]
      have h_card : Finset.card ({a} : Finset α) ≤ Finset.card s := by
        have hpos : 0 < Finset.card s := Finset.card_pos.mpr ⟨a, ha_mem⟩
        have h_card_single : Finset.card ({a} : Finset α) = 1 := by simp
        rw [h_card_single]
        have : 1 ≤ Finset.card s := by omega
        exact this
      exact Finset.eq_of_subset_of_card_le h_sub h_card
    rcases h_exists with ⟨x, hx, hx_ne_a⟩
    have hx_not_fixed : f x ≠ x := by
      intro h_eq; apply hx_ne_a; exact h_unique x hx h_eq
    have hfx_mem_s : f x ∈ s := hfs x hx
    have hfx_ne_x : f x ≠ x := hx_not_fixed
    let s' := (s.erase x).erase (f x)
    have h_card_ge_2 : 2 ≤ s.card := by
      have h := Finset.one_lt_card.mpr ⟨a, ha_mem, x, hx, hx_ne_a.symm⟩
      omega
    have h_card_relation : s.card = s'.card + 2 := by
      have hfx_mem_serasex : f x ∈ s.erase x :=
        Finset.mem_erase.mpr ⟨hfx_ne_x, hfx_mem_s⟩
      have h_card_erase : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
      have h_card_erase2 : s'.card = (s.erase x).card - 1 := Finset.card_erase_of_mem hfx_mem_serasex
      rw [h_card_erase2, h_card_erase]
      have hcalc : (s.card - 1) - 1 + 2 = s.card := by
        have hcard_ge_1 : 1 ≤ s.card := by
          have : 0 < s.card := Finset.card_pos.mpr ⟨x, hx⟩
          omega
        omega
      exact hcalc.symm
    have ha_mem_s' : a ∈ s' := by
      have ha_ne_x : a ≠ x := Ne.symm hx_ne_a
      have ha_ne_fx : a ≠ f x := by
        intro h_eq
        apply ha_ne_x
        calc
          a = f a := ha_fixed.symm
          _ = f (f x) := by rw [h_eq]
          _ = x := h_invol x
      apply Finset.mem_erase.mpr
      refine ⟨ha_ne_fx, ?_⟩
      apply Finset.mem_erase.mpr
      exact ⟨ha_ne_x, ha_mem⟩
    have hfs' : ∀ y ∈ s', f y ∈ s' := by
      intro y hy
      rcases Finset.mem_erase.mp hy with ⟨hy_ne_fx, hy_mem_erase_x⟩
      rcases Finset.mem_erase.mp hy_mem_erase_x with ⟨hy_ne_x, hy_mem_s⟩
      have hfy_mem_s : f y ∈ s := hfs y hy_mem_s
      have hfy_ne_x : f y ≠ x := by
        intro h_eq
        apply hy_ne_fx
        calc
          y = f (f y) := by rw [h_invol y]
          _ = f x := by rw [h_eq]
      have hfy_ne_fx : f y ≠ f x := by
        intro h_eq
        apply hy_ne_x
        calc
          y = f (f y) := by rw [h_invol y]
          _ = f (f x) := by rw [h_eq]
          _ = x := h_invol x
      apply Finset.mem_erase.mpr
      refine ⟨hfy_ne_fx, ?_⟩
      apply Finset.mem_erase.mpr
      exact ⟨hfy_ne_x, hfy_mem_s⟩
    have h_unique' : ∀ y ∈ s', f y = y → y = a := by
      intro y hy hy_fixed
      apply h_unique y ?_ hy_fixed
      rcases Finset.mem_erase.mp hy with ⟨_, hy_mem_erase_x⟩
      rcases Finset.mem_erase.mp hy_mem_erase_x with ⟨_, hy_mem_s⟩
      exact hy_mem_s
    have h_ih : Odd s'.card :=
      card_odd_of_involution_unique_fixed s' f hfs' h_invol a ha_mem_s' ha_fixed h_unique'
    rcases h_ih with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    rw [hk] at h_card_relation
    omega
termination_by s.card
decreasing_by
  have hx_not_mem_s' : x ∉ s' := by
    simp [s']
  have hx_mem_s : x ∈ s := hx
  have h_sub : s' ⊆ s := by
    intro y hy
    apply Finset.mem_of_mem_erase
    apply Finset.mem_of_mem_erase
    exact hy
  have h_not_sub : ¬(s ⊆ s') := by
    intro h_sub_s_s'
    apply hx_not_mem_s'
    apply h_sub_s_s'
    exact hx_mem_s
  have h_ssub : s' ⊂ s := ⟨h_sub, h_not_sub⟩
  exact Finset.card_lt_card h_ssub

/-- An equivalence between `comap toConjAct (stabilizer t)` and `stabilizer t`. -/
def comapEquiv (G : Type*) [Group G] (t : G) :
    Subgroup.comap ConjAct.toConjAct.toMonoidHom (MulAction.stabilizer (ConjAct G) t) ≃
    MulAction.stabilizer (ConjAct G) t :=
  { toFun := λ x => ⟨ConjAct.toConjAct x.1, x.2⟩
    invFun := λ y => ⟨ConjAct.ofConjAct y.1, by
      have h_mem : y.1 ∈ MulAction.stabilizer (ConjAct G) t := y.2
      have h_eq : y.1 • t = t := (MulAction.mem_stabilizer_iff (G := ConjAct G) (a := t)).mp h_mem
      apply (MulAction.mem_stabilizer_iff (G := ConjAct G) (a := t)).mpr
      calc
        (ConjAct.toConjAct (ConjAct.ofConjAct y.1)) • t = y.1 • t := by simp
        _ = t := h_eq⟩
    left_inv := λ x => by
      ext; simp
    right_inv := λ y => by
      ext; simp }

/-- The index of the centralizer of an isolated involution is odd. -/
theorem odd_index_of_centralizer (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t) :
    Odd (Subgroup.index (Subgroup.centralizer {t})) := by
  have hinv : t⁻¹ = t := by
    apply inv_eq_of_mul_eq_one_left
    rw [ht2]

  -- The conjugacy class of t as a Finset
  let C : Finset G := Finset.image (λ g : G => g * t * g⁻¹) Finset.univ

  -- The involution φ(x) = t*x*t (conjugation by t, since t⁻¹ = t)
  set φ : G → G := λ x => t * x * t with hφ

  have hφ_invol : ∀ x : G, φ (φ x) = x := by
    intro x; dsimp [φ]; calc
      t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = 1 * x * 1 := by rw [ht2]
      _ = x := by simp

  have hC_t_mem : t ∈ C := by
    refine Finset.mem_image.mpr ⟨1, Finset.mem_univ _, ?_⟩
    simp

  have hφ_t_fixed : φ t = t := by
    dsimp [φ]; simp [ht2]

  have hφ_maps_C : ∀ x ∈ C, φ x ∈ C := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨g, hg, hx_eq⟩
    subst hx_eq
    refine Finset.mem_image.mpr ⟨t * g, Finset.mem_univ _, ?_⟩
    calc
      (t * g) * t * (t * g)⁻¹ = (t * g) * t * (g⁻¹ * t⁻¹) := by simp
      _ = (t * g) * t * (g⁻¹ * t) := by rw [hinv]
      _ = t * (g * t * g⁻¹) * t := by group
      _ = φ (g * t * g⁻¹) := rfl

  have hφ_fixed_only_t : ∀ x ∈ C, φ x = x → x = t := by
    intro x hx hfix
    rcases Finset.mem_image.mp hx with ⟨g, hg, hx_eq⟩
    subst hx_eq
    have hcomm : (g * t * g⁻¹) * t = t * (g * t * g⁻¹) := by
      dsimp [φ] at hfix
      -- hfix: t*(g*t*g⁻¹)*t = g*t*g⁻¹
      calc
        (g * t * g⁻¹) * t = (t * (g * t * g⁻¹) * t) * t := by
          exact congrArg (· * t) hfix.symm
        _ = (t * (g * t * g⁻¹)) * (t * t) := by group
        _ = (t * (g * t * g⁻¹)) * 1 := by rw [ht2]
        _ = t * (g * t * g⁻¹) := by simp
    exact hisolated g hcomm

  -- Step 1: The conjugacy class has odd cardinality
  have hC_odd : Odd C.card :=
    card_odd_of_involution_unique_fixed C φ hφ_maps_C hφ_invol t hC_t_mem hφ_t_fixed hφ_fixed_only_t

  -- Step 2: Relate C.card to Subgroup.index (Subgroup.centralizer {t})
  have hcardC_eq_index : C.card = Subgroup.index (Subgroup.centralizer {t}) := by
    -- Orbit-stabilizer: |orbit(t)| * |stabilizer(t)| = |G|
    have horbit_stab : Nat.card (MulAction.orbit (ConjAct G) t : Set G) *
      Nat.card (MulAction.stabilizer (ConjAct G) t) = Nat.card G := by
      haveI : Fintype (MulAction.orbit (ConjAct G) t : Set G) :=
        (Set.toFinite (MulAction.orbit (ConjAct G) t : Set G)).fintype
      haveI : Fintype (MulAction.stabilizer (ConjAct G) t) :=
        (Set.toFinite ((MulAction.stabilizer (ConjAct G) t : Set (ConjAct G)) : Set (ConjAct G))).fintype
      have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) t
      simpa [Nat.card_eq_fintype_card] using h

    -- The stabilizer is isomorphic to the centralizer
    have h_card_stab_eq_centralizer : Nat.card (MulAction.stabilizer (ConjAct G) t) =
      Nat.card (Subgroup.centralizer {t}) := by
      have h_eq : Subgroup.centralizer {t} = Subgroup.comap ConjAct.toConjAct.toMonoidHom
        (MulAction.stabilizer (ConjAct G) t) :=
        Subgroup.centralizer_eq_comap_stabilizer t
      rw [h_eq]
      have h_card_comap : Nat.card (Subgroup.comap ConjAct.toConjAct.toMonoidHom
        (MulAction.stabilizer (ConjAct G) t)) = Nat.card (MulAction.stabilizer (ConjAct G) t) :=
        Nat.card_congr (comapEquiv G t)
      exact h_card_comap.symm

    -- The orbit equals the conjugacy class C (as a set)
    have h_orbit_eq_C : (MulAction.orbit (ConjAct G) t : Set G) = (C : Set G) := by
      ext x
      constructor
      · intro hx
        rcases MulAction.mem_orbit_iff.mp hx with ⟨g, rfl⟩
        simp [C, ConjAct.smul_def]
      · intro hx
        have hx_mem : x ∈ Finset.image (λ g : G => g * t * g⁻¹) Finset.univ := by
          simpa [C] using hx
        rcases Finset.mem_image.1 hx_mem with ⟨g, _, hg_eq⟩
        rw [← hg_eq]
        refine MulAction.mem_orbit_iff.mpr ⟨ConjAct.toConjAct g, ?_⟩
        simp [ConjAct.smul_def]

    -- C.card equals Nat.card of the orbit
    have hC_card_eq_natcard_orbit : C.card = Nat.card (MulAction.orbit (ConjAct G) t : Set G) := by
      calc
        C.card = Fintype.card (C : Set G) := by simp
        _ = Nat.card (C : Set G) := by simp
        _ = Nat.card (MulAction.orbit (ConjAct G) t : Set G) := by rw [h_orbit_eq_C]

    -- Lagrange: index * |centralizer| = |G|
    have h_index_centralizer : Subgroup.index (Subgroup.centralizer {t}) *
      Nat.card (Subgroup.centralizer {t}) = Nat.card G :=
      Subgroup.index_mul_card (Subgroup.centralizer {t})

    -- Product equality: C.card * |centralizer| = index * |centralizer|
    have h_product_eq : C.card * Nat.card (Subgroup.centralizer {t}) =
      Subgroup.index (Subgroup.centralizer {t}) * Nat.card (Subgroup.centralizer {t}) := by
      calc
        C.card * Nat.card (Subgroup.centralizer {t})
            = Nat.card (MulAction.orbit (ConjAct G) t : Set G) * Nat.card (Subgroup.centralizer {t}) := by
              rw [hC_card_eq_natcard_orbit]
        _ = Nat.card (MulAction.orbit (ConjAct G) t : Set G) * Nat.card (MulAction.stabilizer (ConjAct G) t) := by
          rw [h_card_stab_eq_centralizer]
        _ = Nat.card G := horbit_stab
        _ = Subgroup.index (Subgroup.centralizer {t}) * Nat.card (Subgroup.centralizer {t}) := by
          rw [Subgroup.index_mul_card (Subgroup.centralizer {t})]

    have h_card_centralizer_pos : 0 < Nat.card (Subgroup.centralizer {t}) := by
      haveI : Nonempty (Subgroup.centralizer {t}) := ⟨⟨1, by simp⟩⟩
      haveI : Finite (Subgroup.centralizer {t}) := inferInstance
      exact Nat.card_pos

    -- Cancel the centralizer cardinality (positive) to get C.card = index
    exact mul_right_cancel₀ h_card_centralizer_pos.ne' h_product_eq

  -- Combine steps 1 and 2
  rw [← hcardC_eq_index]
  exact hC_odd

end Submission.OddIndex
