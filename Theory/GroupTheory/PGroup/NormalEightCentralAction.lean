module

public import Theory.GroupTheory.PGroup.NormalEightAbelianReduction

/-!
# Central involution actions without normal elementary eights

Let D be a normal abelian self-centralizing subgroup, with first omega
subgroup equal to the central omega four. An involution whose action on D
commutes with the whole ambient conjugation image lies in D if every element
of D it inverts has square one.

Indeed, centrality of the action puts every conjugation difference in D.
Squaring a conjugate shows that the involution inverts the difference. Hence
the differences lie in the central omega four, and adjoining the involution
gives a normal elementary subgroup. Absence of normal elementary eights
forces this subgroup back into the central four.

This is the normal-subgroup obstruction used in the homocyclic reduction of
the MacWilliams–Sah bound quoted by Janko–Thompson, Math. Z. 113 (1970),
1.1, printed p.385, in
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
The proof generalizes the cyclic argument in `CyclicSelfCentralizerFour`.
-/

open Subgroup

namespace IsPGroup

/-- Ambient conjugation fixes every involution in the normal abelian subgroup. -/
public theorem conjNormal_fixed_of_square_eq_one_of_no_normal_eight {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (g : P) (d : D) (hd : d ^ 2 = 1) : MulAut.conjNormal g d = d := by
  have hO := IsPGroup.omega_one_normal_abelian_eq_center_of_no_normal_eight hno hZ D hD
  have hmem : (d : P) ∈ (omega₁ D (p := 2)).map D.subtype := by
    refine ⟨d, subset_closure ?_, rfl⟩
    simpa using hd
  rw [hO] at hmem
  have hcent := map_subtype_le (omega₁ (center P) (p := 2)) hmem
  apply Subtype.ext
  change g * (d : P) * g⁻¹ = d
  rw [mem_center_iff.mp hcent g, mul_inv_cancel_right]

/-- A normal elementary subgroup has trivial conjugation image when the central
omega four contains every normal elementary subgroup. -/
public theorem conj_image_card_eq_one_of_elementary_normal_of_no_normal_eight {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsElementaryAbelian 2 D]
    (A : Subgroup P) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range = 1 := by
  have hDC : D ≤ center P := (normal_elementary_le_omega_center_of_no_normal_eight
    hno hZ D).trans (map_subtype_le _)
  have hf : ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range = ⊥ := by
    apply MonoidHom.range_eq_bot_iff.mpr
    apply MonoidHom.ext
    intro a
    ext d
    change (a : P) * (d : P) * (a : P)⁻¹ = d
    rw [mem_center_iff.mp (hDC d.property) a, mul_inv_cancel_right]
  rw [hf]
  exact Nat.card_unique


/-- An involution with central action and only binary inverted elements belongs
to the normal abelian subgroup when normal elementary eights are absent. -/
public theorem involution_mem_normal_abelian_of_central_action_of_no_normal_eight
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (x : P) (hx : x ^ 2 = 1)
    (hcomm : ∀ g : P, Commute (MulAut.conjNormal (H := D) g)
      (MulAut.conjNormal (H := D) x))
    (hinv : ∀ d ∈ D, x * d * x⁻¹ = d⁻¹ → d ^ 2 = 1) : x ∈ D := by
  let O := (omega₁ D (p := 2)).map D.subtype
  have hOeq := IsPGroup.omega_one_normal_abelian_eq_center_of_no_normal_eight hno hZ D hD
  have hOc : O ≤ center P := by
    rw [show O = (omega₁ (center P) (p := 2)).map (center P).subtype from hOeq]
    exact map_subtype_le _
  let : IsElementaryAbelian 2 (omega₁ D (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx
  have hCO : zpowers x ≤ centralizer (O : Set P) := by
    apply zpowers_le.mpr
    intro o ho
    exact (mem_center_iff.mp (hOc ho) x).symm
  let U := O ⊔ zpowers x
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.sup_of_le_centralizer hCO
  have hdiff (g : P) : g * x * g⁻¹ * x⁻¹ ∈ O := by
    let d := g * x * g⁻¹ * x⁻¹
    let f : P →* MulAut D := MulAut.conjNormal
    have hker : f d = 1 := by
      dsimp [d, f]
      simp only [map_mul, map_inv]
      rw [(hcomm g).eq]
      group
    have hd : d ∈ D := by
      apply hD
      intro a ha
      have hh := congrArg (fun t : MulAut D => (t ⟨a, ha⟩ : P)) hker
      change d * a * d⁻¹ = a at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hde : (d * x) ^ 2 = 1 := by
      change (g * x * g⁻¹ * x⁻¹ * x) ^ 2 = 1
      rw [inv_mul_cancel_right, ← MulAut.conj_apply, ← map_pow, hx, map_one]
    have hdi : x * d * x⁻¹ = d⁻¹ := by
      have hprod : d * (x * d * x⁻¹) = 1 := by
        calc
          d * (x * d * x⁻¹) = (d * x) ^ 2 * (x ^ 2)⁻¹ := by
            simp only [pow_two]; group
          _ = 1 := by rw [hde, hx]; simp
      exact eq_inv_of_mul_eq_one_right hprod
    refine ⟨⟨d, hd⟩, subset_closure ?_, rfl⟩
    change (⟨d, hd⟩ : D) ^ (2 ^ 1) = 1
    apply Subtype.ext
    simpa using hinv d hd hdi
  let : U.Normal := by
    constructor
    intro y hy g
    have hmap : U.map (MulAut.conj g).toMonoidHom ≤ U := by
      rw [show U = O ⊔ zpowers x from rfl, Subgroup.map_sup, MonoidHom.map_zpowers]
      apply sup_le
      · rintro _ ⟨o, ho, rfl⟩
        have hh : MulAut.conj g o = o := by
          change g * o * g⁻¹ = o
          rw [mem_center_iff.mp (hOc ho) g, mul_inv_cancel_right]
        change MulAut.conj g o ∈ U
        rw [hh]
        exact (le_sup_left : O ≤ U) ho
      · apply zpowers_le.mpr
        have hh : MulAut.conj g x = (g * x * g⁻¹ * x⁻¹) * x := by
          simp [MulAut.conj_apply]
        change MulAut.conj g x ∈ U
        rw [hh]
        exact U.mul_mem ((le_sup_left : O ≤ U) (hdiff g))
          ((le_sup_right : zpowers x ≤ U) (mem_zpowers x))
    exact hmap (mem_map_of_mem _ hy)
  have hU := normal_elementary_le_omega_center_of_no_normal_eight hno hZ U
  have hUO : U ≤ O := by simpa only [← hOeq] using hU
  exact (map_subtype_le _) (hUO ((le_sup_right : zpowers x ≤ U) (mem_zpowers x)))

end IsPGroup
