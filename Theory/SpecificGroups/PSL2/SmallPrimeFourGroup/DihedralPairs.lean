module

public import Glauberman.DicksonClassification
public import Glauberman.DicksonSplitTorus
public import Glauberman.DicksonNonsplitTorus
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.ThreeConjugateGeneration
public import Theory.SpecificGroups.PSL2.InvolutionFusion
import Mathlib.Tactic

/-!
# Maximal dihedral pairs at four small prime parameters

For q = 13, 17, 19, 23, the torus with odd order has order 7, 9, 9, 11.
Its reflected normalizer has order 14, 18, 18, 22. Dickson's classification
proves maximality by divisibility, including all exceptional and subfield
alternatives. Involution fusion then places the involution of any subgroup
of order four at each generator. The subgroup of order four cannot lie in
the normalizer, so the two conjugates generate PSL₂.

This is the inner four-group branch of Guralnick--Malle, *Classification of
2F-modules I*, Proposition 4.1, manuscript pp.8--9, used in Aschbacher--Smith
K.2, printed p.453. Diagonal outer actors require a separate normalizer
escape argument; this module makes no assertion that they are inner.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.PSL2.SmallPrimeFourGroup

/-- The dihedral order with odd rotation subgroup: 14, 18, 18, and 22. -/
@[expose] def lowOrder (q : ℕ) : ℕ := if q % 4 = 1 then q + 1 else q - 1

/-- Subgroups of the low dihedral order are maximal at the four source parameters. -/
theorem maximal_of_card {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23)
    (hF : Nat.card F = p)
    (D : Subgroup (PSL2MatrixGroup F)) (hD : Nat.card D = lowOrder p) :
    IsCoatom D := by
  classical
  have ho : Odd p := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hlarge : 11 < p := by rcases hp with rfl | rfl | rfl | rfl <;> omega
  have hqodd : Odd (Nat.card F) := hF ▸ ho
  have hcard := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) hqodd
  rw [hF] at hcard
  have hgcd : Nat.gcd (p - 1) 2 = 2 := by
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hdpos : 0 < lowOrder p := by
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hbound : p + 1 < 2 * lowOrder p := by
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hhalf : (p - 1) / 2 < lowOrder p := by
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hcop : (lowOrder p).Coprime p := by
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hDne : D ≠ ⊤ := by
    intro ht
    have hc : Nat.card (PSL2MatrixGroup F) = lowOrder p := by simpa [ht] using hD
    rw [hc] at hcard
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num [lowOrder] at hcard
  refine ⟨hDne, ?_⟩
  intro H hDH
  have hlt : lowOrder p < Nat.card H := by
    rw [← hD]
    by_contra! hge
    exact hDH.ne (eq_of_le_of_card_ge hDH.le hge)
  have hdvd : lowOrder p ∣ Nat.card H := hD ▸ card_dvd_of_le hDH.le
  have hdouble : 2 * lowOrder p ≤ Nat.card H := by
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : 2 ≤ k := by
      by_contra! hk2
      interval_cases k <;> simp_all
    nlinarith
  have hFp : Nat.card F = p ^ 1 := by simpa using hF
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hFp H with
    hElem | hCyc | hDih | hA4 | hS4 | hA5 | hBorel | hPSL | hPGL
  · let : IsElementaryAbelian p H := hElem
    obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup p H).exists_card_eq
    rw [hm] at hdvd
    have hh := (hcop.pow_right m).eq_one_of_dvd hdvd
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num [lowOrder] at hh
  · obtain ⟨z, hz, hc, _⟩ := hCyc
    rw [hF, hgcd] at hz
    rcases hz with hz | hz
    all_goals
      have hboundz := Nat.le_of_dvd (by omega) hz
      omega
  · obtain ⟨z, hz, hc, _⟩ := hDih
    rw [hF, hgcd] at hz
    rcases hz with hz | hz
    all_goals
      have hboundz := Nat.le_of_dvd (by omega) hz
      omega
  · obtain ⟨_, ⟨f⟩⟩ := hA4
    have hc := Nat.card_congr f.toEquiv
    rw [nat_card_alternatingGroup, Nat.card_fin] at hc
    norm_num at hc
    rw [hc] at hdvd
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num [lowOrder] at hdvd
  · obtain ⟨_, ⟨f⟩⟩ := hS4
    have hc := Nat.card_congr f.toEquiv
    rw [Nat.card_perm, Nat.card_fin] at hc
    norm_num at hc
    rw [hc] at hdvd
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num [lowOrder] at hdvd
  · obtain ⟨_, ⟨f⟩⟩ := hA5
    have hc := Nat.card_congr f.toEquiv
    rw [nat_card_alternatingGroup, Nat.card_fin] at hc
    norm_num at hc
    rw [hc] at hdvd
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num [lowOrder] at hdvd
  · obtain ⟨m, t, _, ht, N, C, hN, _, hcN, _, hcC, hdisj, hsup⟩ := hBorel
    let : N.Normal := hN
    have hc : Nat.card H = p ^ m * t := by
      have hh := card_sup_eq_mul_of_normalizes_of_disjoint N C
        (by rw [N.normalizer_eq_top]; exact le_top) hdisj
      simpa [hsup, hcN, hcC] using hh
    rw [hc] at hdvd
    have hd := (hcop.pow_right m).dvd_of_dvd_mul_left hdvd
    have htpos : 0 < t := hcC ▸ Nat.card_pos (α := C)
    have hlow := Nat.le_of_dvd htpos hd
    simp only [pow_one, hgcd] at ht
    have hhigh := Nat.le_of_dvd (by omega : 0 < (p - 1) / 2) ht
    omega
  · obtain ⟨m, hm0, hmdiv, ⟨f⟩⟩ := hPSL
    have hm : m = 1 := Nat.dvd_one.mp hmdiv
    subst m
    have hmcard := GaloisField.card p 1 (by decide)
    have hmOdd : Odd (Nat.card (GaloisField p 1)) := hmcard ▸ ho.pow
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (F := GaloisField p 1) hmOdd
    rw [hmcard, ← Nat.card_congr f.toEquiv] at hc
    simp only [pow_one] at hc
    apply eq_top_of_card_eq H
    exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) (hc.trans hcard.symm)
  · obtain ⟨m, hm0, hmdiv, _⟩ := hPGL
    have := Nat.dvd_one.mp hmdiv
    omega

/-- A cyclic torus of odd order with its reflection and exact normalizer. -/
theorem exists_low_torus {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23)
    (hF : Nat.card F = p) :
    ∃ C : Subgroup (PSL2MatrixGroup F), ∃ w : PSL2MatrixGroup F,
      IsCyclic C ∧ Nat.card C = lowOrder p / 2 ∧ w ∉ C ∧ w ^ 2 = 1 ∧
      (∀ x ∈ C, w * x * w⁻¹ = x⁻¹) ∧
      Nat.card (C ⊔ zpowers w : Subgroup (PSL2MatrixGroup F)) = lowOrder p ∧
      IsCoatom (C ⊔ zpowers w) ∧
      (∀ R : Subgroup (PSL2MatrixGroup F), R ≤ C → R ≠ ⊥ →
        normalizer (R : Set (PSL2MatrixGroup F)) = C ⊔ zpowers w) := by
  have hFp : Nat.card F = p ^ 1 := by simpa using hF
  by_cases hmod : p % 4 = 1
  · obtain ⟨C, w, hcyc, hcard, _, hw, hw2, hinv, hD, hnorm⟩ :=
      Glauberman.Dickson.huppert_II_8_4_nonsplit_torus_reflection_data hFp
    have hC : Nat.card C = lowOrder p / 2 := by
      rw [hcard, hF]
      rcases hp with rfl | rfl | rfl | rfl <;> norm_num [lowOrder] at *
    have hDc : Nat.card (C ⊔ zpowers w : Subgroup (PSL2MatrixGroup F)) = lowOrder p := by
      rw [hD, hC]
      rcases hp with rfl | rfl | rfl | rfl <;> norm_num [lowOrder]
    exact ⟨C, w, hcyc, hC, hw, by simpa [pow_two] using hw2, hinv, hDc,
      maximal_of_card hp hF _ hDc, hnorm⟩
  · obtain ⟨C, w, hcyc, hcard, _, hw, hw2, hinv, hD, hnorm⟩ :=
      Glauberman.Dickson.huppert_II_8_3_split_torus_reflection_data hFp
    have hC : Nat.card C = lowOrder p / 2 := by
      rw [hcard, hF]
      rcases hp with rfl | rfl | rfl | rfl <;> norm_num [lowOrder] at *
    have hDc : Nat.card (C ⊔ zpowers w : Subgroup (PSL2MatrixGroup F)) = lowOrder p := by
      rw [hD, hC]
      rcases hp with rfl | rfl | rfl | rfl <;> norm_num [lowOrder]
    exact ⟨C, w, hcyc, hC, hw, by simpa [pow_two] using hw2, hinv, hDc,
      maximal_of_card hp hF _ hDc, hnorm⟩

/-- Two involutions generate a maximal subgroup of the low dihedral order. -/
theorem exists_maximal_pair {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23)
    (hF : Nat.card F = p) :
    ∃ a b : PSL2MatrixGroup F, a ≠ 1 ∧ a ^ 2 = 1 ∧ b ≠ 1 ∧ b ^ 2 = 1 ∧
      IsCoatom (closure ({a, b} : Set (PSL2MatrixGroup F))) ∧
      Nat.card (closure ({a, b} : Set (PSL2MatrixGroup F))) = lowOrder p := by
  obtain ⟨C, w, hcyc, _, hw, hw2, hinv, hcard, hmax, _⟩ := exists_low_torus hp hF
  let : IsCyclic C := hcyc
  obtain ⟨a, b, ha, ha2, hb, hb2, heq⟩ :=
    Theory.GroupTheory.ThreeConjugateGeneration.pair_of_cyclic_inverter C w hw hw2 hinv
  exact ⟨a, b, ha, ha2, hb, hb2, heq ▸ hmax, heq ▸ hcard⟩

/-- Two conjugates of every order-four subgroup generate the actual PSL₂ group. -/
theorem exists_two_conjugates {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23)
    (hF : Nat.card F = p) (A : Subgroup (PSL2MatrixGroup F)) (hA : Nat.card A = 4) :
    ∃ c : Fin 2 → PSL2MatrixGroup F,
      (⨆ i, A.map (MulAut.conj (c i)).toMonoidHom) = ⊤ := by
  classical
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (by omega : 2 ∣ Nat.card A)
  have htorder : orderOf (t : PSL2MatrixGroup F) = 2 := (Subgroup.orderOf_coe t).trans ht
  obtain ⟨a, b, ha, ha2, hb, hb2, hmax, hcard⟩ := exists_maximal_pair hp hF
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp (involutions_isConj (t : PSL2MatrixGroup F) a
    htorder (orderOf_eq_prime ha2 ha))
  obtain ⟨g₁, hg₁⟩ := isConj_iff.mp (involutions_isConj (t : PSL2MatrixGroup F) b
    htorder (orderOf_eq_prime hb2 hb))
  let c : Fin 2 → PSL2MatrixGroup F := ![g₀, g₁]
  let H := ⨆ i, A.map (MulAut.conj (c i)).toMonoidHom
  have hgen (i : Fin 2) : c i * (t : PSL2MatrixGroup F) * (c i)⁻¹ ∈ H :=
    (le_iSup (fun i => A.map (MulAut.conj (c i)).toMonoidHom) i)
      (mem_map.mpr ⟨t, t.2, rfl⟩)
  have haH : a ∈ H := by simpa [c, hg₀] using hgen 0
  have hbH : b ∈ H := by simpa [c, hg₁] using hgen 1
  have hpair : closure ({a, b} : Set (PSL2MatrixGroup F)) ≤ H :=
    (closure_le _).mpr (by
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨haH, hbH⟩)
  refine ⟨c, hmax.lt_iff.mp (lt_of_le_of_ne hpair ?_)⟩
  intro heq
  have hle : A.map (MulAut.conj (c 0)).toMonoidHom ≤
      closure ({a, b} : Set (PSL2MatrixGroup F)) :=
    heq ▸ le_iSup (fun i => A.map (MulAut.conj (c i)).toMonoidHom) 0
  have hd := card_dvd_of_le hle
  rw [card_map_of_injective (MulAut.conj (c 0)).injective, hA, hcard] at hd
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num [lowOrder] at hd

end Theory.PSL2.SmallPrimeFourGroup
