module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic

/-!
# Elementary involution lifts over irreducible central sections

A central commutator map A → Z has kernel C_A(i). When the section A/Z
is irreducible under an actor centralizing i, this kernel is Z or A. The
first alternative would give |A| ≤ |Z|², so a larger section is fixed by i.
If U has commutators in Z and i fixes [U,i], the three-subgroups lemma
makes [U,i] abelian. The involution relation then gives exponent two.

Source: the elementary lift step in Aschbacher–Smith, Lemma 14.4.9,
combined manuscript (1 March 2004), printed p.1010.
-/

public section
open scoped commutatorElement IsMulCommutative
namespace Subgroup

/-- An irreducible central section of size greater than the central kernel
has no nontrivial central discrepancy with a commuting actor. -/
theorem centralizes_of_irreducible_section {G : Type*} [Group G] [Finite G]
    (A Z K : Subgroup G) (i : G)
    (hZA : Z ≤ A) (hZAcent : Z ≤ centralizer (A : Set G))
    (hZi : Z ≤ centralizer ({i} : Set G))
    (hAi : ⁅A, zpowers i⁆ ≤ Z)
    (hKA : K ≤ normalizer (A : Set G))
    (hKi : K ≤ centralizer ({i} : Set G))
    (hcard : Nat.card Z * Nat.card Z < Nat.card A)
    (hirr : ∀ E : Subgroup G, Z ≤ E → E ≤ A →
      K ≤ normalizer (E : Set G) → E = Z ∨ E = A) :
    A ≤ centralizer ({i} : Set G) := by
  let C := A ⊓ centralizer ({i} : Set G)
  have hKC : K ≤ normalizer (C : Set G) := by
    apply le_normalizer_iff.mpr
    intro k hk a ha
    refine ⟨(mem_normalizer_iff.mp (hKA hk) a).mp ha.1, ?_⟩
    have hkcomm : Commute k i := mem_centralizer_singleton_iff.mp (hKi hk)
    have hacomm : Commute a i := mem_centralizer_singleton_iff.mp ha.2
    exact mem_centralizer_singleton_iff.mpr
      ((hkcomm.mul_left hacomm).mul_left hkcomm.inv_left)
  rcases hirr C (le_inf hZA hZi) inf_le_left hKC with he | he
  · let f : A →* Z := {
      toFun a := ⟨⁅(a : G), i⁆, hAi (commutator_mem_commutator a.property (mem_zpowers i))⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' a b := by
        apply Subtype.ext
        change ⁅(a : G) * b, i⁆ = ⁅(a : G), i⁆ * ⁅(b : G), i⁆
        have hb := hAi (commutator_mem_commutator b.property (mem_zpowers i))
        have hc := mem_centralizer_iff.mp (hZAcent hb) a a.property
        rw [commutatorElement_mul_left_eq_conj_mul, hc]
        simp only [mul_inv_cancel_right]
        exact (mem_centralizer_iff.mp (hZAcent hb) _
          (hZA (hAi (commutator_mem_commutator a.property (mem_zpowers i))))).symm }
    have hker : f.ker = Z.subgroupOf A := by
      ext a
      change (⟨⁅(a : G), i⁆, _⟩ : Z) = 1 ↔ (a : G) ∈ Z
      rw [Subtype.ext_iff]
      change ⁅(a : G), i⁆ = 1 ↔ (a : G) ∈ Z
      rw [commutatorElement_eq_one_iff_mul_comm]
      have hc : (a : G) ∈ C ↔ (a : G) ∈ Z := by rw [he]
      simpa only [C, mem_inf, a.property, true_and, mem_centralizer_singleton_iff, eq_comm] using hc
    have hkerCard : Nat.card f.ker = Nat.card Z := by
      rw [hker]
      exact Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv
    have hbound : Nat.card f.range ≤ Nat.card Z := card_le_of_le le_top |>.trans_eq (by simp)
    have hm := f.ker.card_mul_index
    rw [index_ker, hkerCard] at hm
    exact False.elim (hcard.not_ge (hm ▸ Nat.mul_le_mul_left _ hbound))
  · exact he ▸ (inf_le_right : C ≤ centralizer ({i} : Set G))

/-- Once the moved group is fixed, the three-subgroups lemma makes it abelian;
the involution relation makes every commutator generator have square one. -/
theorem elementary_commutator_of_fixed {G : Type*} [Group G]
    (U Z : Subgroup G) (i : G) (hi : i ^ 2 = 1)
    (hUi : ⁅U, zpowers i⁆ ≤ U) (hUU : ⁅U,U⁆ ≤ Z)
    (hZi : Z ≤ centralizer ({i} : Set G))
    (hfixed : ⁅U, zpowers i⁆ ≤ centralizer ({i} : Set G)) :
    IsElementaryAbelian 2 (⁅U, zpowers i⁆ : Subgroup G) := by
  let B := ⁅U, zpowers i⁆
  have hBC : B ≤ centralizer (zpowers i : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
    exact hfixed
  have hZC : Z ≤ centralizer (zpowers i : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
    exact hZi
  have hBB : ⁅B,B⁆ = ⊥ := by
    change ⁅⁅U,zpowers i⁆,B⁆ = ⊥
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm (zpowers i) B,
        commutator_eq_bot_iff_le_centralizer.mpr hBC, commutator_bot_left]
    · exact commutator_eq_bot_iff_le_centralizer.mpr
        (((commutator_mono hUi le_rfl).trans hUU).trans hZC)
  let : IsMulCommutative B := commutator_self_eq_bot_iff.mp hBB
  have hs (u : G) (hu : u ∈ U) (b : G) (hb : b ∈ zpowers i) : ⁅u,b⁆ ^ 2 = 1 := by
    have hb2 : b ^ 2 = 1 := by
      let : IsElementaryAbelian 2 (zpowers i) := IsElementaryAbelian.zpowers_of_pow_eq_one hi
      exact elemPow_eq_one_of_isElementaryAbelian b hb
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hb2)
    have hc : b * ⁅u,b⁆ = ⁅u,b⁆ * b :=
      mem_centralizer_iff.mp (hBC (commutator_mem_commutator hu hb)) b hb
    have hinv : b * ⁅u,b⁆ * b⁻¹ = ⁅u,b⁆⁻¹ := by
      simp only [commutatorElement_def, mul_inv_rev, inv_inv, hbi]
      simp only [mul_assoc, show b * b = 1 by simpa only [pow_two] using hb2, mul_one]
    have he : ⁅u,b⁆ = ⁅u,b⁆⁻¹ := by
      calc
        ⁅u,b⁆ = b * ⁅u,b⁆ * b⁻¹ := by rw [hc]; group
        _ = ⁅u,b⁆⁻¹ := hinv
    calc
      ⁅u,b⁆ ^ 2 = ⁅u,b⁆ * ⁅u,b⁆ := pow_two _
      _ = ⁅u,b⁆⁻¹ * ⁅u,b⁆ := congrArg (fun t => t * ⁅u,b⁆) he
      _ = 1 := inv_mul_cancel _
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro b
  apply Subtype.ext
  change (b : G)^2 = 1
  apply closure_induction (k := {g | ∃ u ∈ U, ∃ a ∈ zpowers i, ⁅u,a⁆ = g})
    (p := fun g _ => g^2 = 1) (x := (b : G)) _ (by simp) _ _ b.property
  · rintro g ⟨u, hu, a, ha, rfl⟩
    exact hs u hu a ha
  · intro a b ha hb has hbs
    have hc : Commute a b := congrArg Subtype.val
      (mul_comm (⟨a, ha⟩ : B) (⟨b, hb⟩ : B))
    rw [hc.mul_pow, has, hbs, one_mul]
  · intro a _ ha
    simp [inv_pow, ha]

end Subgroup
