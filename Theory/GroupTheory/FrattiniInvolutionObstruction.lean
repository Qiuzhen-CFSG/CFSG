module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Nilpotent

/-!
# An obstruction to involutory lifts in a Frattini quotient

Suppose D = Φ(G) = Z₂(G) is elementary abelian. A generating family in
G/D cannot have involutory lifts for every member and for every product
with one fixed nonidentity member.

A coset with an involutory lift has central squares: its image modulo
Z(G) differs from an involution by a central involution. Thus lifts of
the fixed member and every other member commute modulo Z(G). Frattini
nongeneration says the lifts generate G, so the fixed lift belongs to
Z₂(G) = D, a contradiction.

This is the central-quotient form of the lift-correction and generation
argument in Parrott, *A characterization of the Tits' simple group*
(1972), Lemma 4, printed p.675. It does not require choosing corrections
or a specific order for G.
-/

open Subgroup

namespace Subgroup

/-- Every element in an involutory coset of an elementary subgroup of
the second center has central square. -/
public theorem square_mem_center_of_involutory_coset
    {G : Type*} [Group G] (D : Subgroup G) [D.Normal]
    [IsElementaryAbelian 2 D] (hD : D ≤ Subgroup.upperCentralSeries G 2)
    (x b : G) (hb : b ^ 2 = 1)
    (hcoset : QuotientGroup.mk' D x = QuotientGroup.mk' D b) :
    x ^ 2 ∈ center G := by
  let q := QuotientGroup.mk' (center G)
  let d := x / b
  have hd : d ∈ D := QuotientGroup.eq_iff_div_mem.mp hcoset
  have hdcentral : q d ∈ center (G ⧸ center G) := by
    have hh := hD hd
    rw [← comap_upperCentralSeries_quotient_center 1,
      Subgroup.upperCentralSeries_one] at hh
    exact hh
  have hc : Commute (q d) (q b) :=
    (mem_center_iff.mp hdcentral (q b)).symm
  have hdpow : d ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian d hd
  have hsplit : x = d * b := by simp [d]
  apply (QuotientGroup.eq_one_iff (N := center G) _).mp
  change q (x ^ 2) = 1
  rw [map_pow, hsplit, map_mul, hc.mul_pow, ← map_pow, ← map_pow,
    hdpow, hb, map_one, one_mul]

private theorem commute_of_three_squares
    {G : Type*} [Group G] (a b : G)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : (a * b) ^ 2 = 1) :
    Commute a b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hb)
  have habi : (a * b)⁻¹ = a * b :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hab)
  change a * b = b * a
  simpa only [mul_inv_rev, hai, hbi] using habi.symm

/-- A generating family of involutory cosets has a product with any fixed
nonidentity member that admits no involutory lift. -/
public theorem exists_product_without_involutory_lift
    {G : Type*} [Group G] [Finite G]
    (D : Subgroup G) [D.Normal] [IsElementaryAbelian 2 D]
    (hPhi : D = frattini G) (hUpper : D = Subgroup.upperCentralSeries G 2)
    {I : Type*} (v : I → G ⧸ D)
    (hgen : closure (Set.range v) = ⊤)
    (hlift : ∀ i, ∃ a : G, a ^ 2 = 1 ∧ QuotientGroup.mk' D a = v i)
    (i : I) (hi : v i ≠ 1) :
    ∃ j, ¬ ∃ b : G, b ^ 2 = 1 ∧ QuotientGroup.mk' D b = v i * v j := by
  classical
  choose a ha hqa using hlift
  let q := QuotientGroup.mk' (center G)
  have hmap : (closure (Set.range a)).map (QuotientGroup.mk' D) = ⊤ := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    simpa only [Function.comp_def, hqa] using hgen
  have hsup : closure (Set.range a) ⊔ frattini G = ⊤ := by
    have hh := congrArg (Subgroup.comap (QuotientGroup.mk' D)) hmap
    simpa [hPhi, sup_comm] using hh
  have hgena : closure (Set.range a) = ⊤ := frattini_nongenerating hsup
  by_contra! hall
  let C := (centralizer ({q (a i)} : Set (G ⧸ center G))).comap q
  have hC : closure (Set.range a) ≤ C := by
    apply (closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨b, hb, hqb⟩ := hall j
    have hprod : (a i * a j) ^ 2 ∈ center G :=
      square_mem_center_of_involutory_coset D hUpper.le _ b hb
        (by rw [map_mul, hqa, hqa, hqb])
    have hqpow (k : I) : q (a k) ^ 2 = 1 := by
      rw [← map_pow, ha, map_one]
    have hqprod : (q (a i) * q (a j)) ^ 2 = 1 := by
      rw [← map_mul, ← map_pow]
      exact (QuotientGroup.eq_one_iff (N := center G) _).mpr hprod
    exact mem_centralizer_singleton_iff.mpr
      (commute_of_three_squares _ _ (hqpow i) (hqpow j) hqprod).symm
  have hCtop : C = ⊤ := top_unique (hgena ▸ hC)
  have hai : a i ∈ D := by
    rw [hUpper, ← comap_upperCentralSeries_quotient_center 1,
      Subgroup.upperCentralSeries_one]
    change q (a i) ∈ center (G ⧸ center G)
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center G) y
    have hx : x ∈ C := hCtop ▸ mem_top x
    exact mem_centralizer_singleton_iff.mp hx
  exact hi ((hqa i).symm.trans ((QuotientGroup.eq_one_iff (N := D) _).mpr hai))

end Subgroup
