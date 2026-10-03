module
public import Theory.GroupTheory.PGroup.HomocyclicElementaryFourTorsion
public import Theory.GroupTheory.PGroup.NormalFourAbelianBase
public import Theory.GroupTheory.PGroup.AbelianInvolutionCosetRoots
public import Theory.GroupTheory.PGroup.HomocyclicFourNormProfile

/-!
# Unequal fourth-root counts over a large homocyclic base

Let `D` be a normal self-centralizing homocyclic abelian subgroup of exponent
at least eight, with omega four `W`. Suppose the centralizer of `W` acts
faithfully on the four-torsion after factoring out `D`. Its automorphism image
is elementary abelian: a matrix congruent to the identity modulo two has
square congruent to the identity modulo four. The homocyclic action bound then
gives image order at most four. An elementary sixteen containing `W` supplies
all four image elements, so the centralizer is the product of `D` and that
sixteen.

The homocyclic norm-profile theorem distinguishes two nonidentity involutions
of the base. Their membership in the omega four and the involutory coset
counting equivalence give unequal fourth-root counts in the centralizer.

Source context: Janko–Thompson, Math. Z. 113 (1970), 1.4, printed p.386 and
the final paragraph of p.395. The congruence argument here is direct and uses
only the stated faithfulness hypothesis, without an exclusion of normal eights.
-/

namespace HomocyclicFourTorsion

private abbrev r2 : ZMod 8 →+* ZMod 2 := ZMod.castHom (by decide) _
private abbrev r4 : ZMod 8 →+* ZMod 4 := ZMod.castHom (by decide) _

set_option maxRecDepth 4096 in
private theorem diag_sq : ∀ a b c : ZMod 8, r2 a = 1 → r2 b = 0 → r2 c = 0 →
    r4 (a*a+b*c) = 1 := by decide

set_option maxRecDepth 4096 in
private theorem offdiag_sq : ∀ a b d : ZMod 8, r2 a = 1 → r2 b = 0 → r2 d = 1 →
    r4 (a*b+b*d) = 0 := by decide

private theorem matrix_sq_mod_four (A : Matrix (Fin 2) (Fin 2) (ZMod 8))
    (hA : A.map r2 = 1) : (A*A).map r4 = 1 := by
  have h00 : r2 (A 0 0) = 1 := congrFun (congrFun hA 0) 0
  have h01 : r2 (A 0 1) = 0 := congrFun (congrFun hA 0) 1
  have h10 : r2 (A 1 0) = 0 := congrFun (congrFun hA 1) 0
  have h11 : r2 (A 1 1) = 1 := congrFun (congrFun hA 1) 1
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using diag_sq _ _ _ h00 h01 h10
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using offdiag_sq _ _ _ h00 h01 h11
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, mul_comm, add_comm] using
      offdiag_sq _ _ _ h11 h10 h00
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, add_comm] using
      diag_sq _ _ _ h11 h10 h01

/-- Faithfulness on four-torsion makes an involution-fixing homocyclic action elementary. -/
public theorem elementary_of_homocyclic_four_torsion
    {D : Type*} [Group D] [Finite D] [IsMulCommutative D]
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (A : Subgroup (MulAut D))
    (hfix : ∀ a ∈ A, ∀ d : D, d ^ 2 = 1 → a d = d)
    (hfaith : ∀ a ∈ A, (∀ d : D, d ^ 4 = 1 → a d = d) → a = 1) :
    IsElementaryAbelian 2 A := by
  obtain ⟨f, h2, h4⟩ := exists_mod_eight_matrix_action n hn e A hfix hfaith
  have hs (a : A) : a ^ 2 = 1 := by
    apply h4 (a ^ 2)
    simpa only [pow_two, map_mul] using matrix_sq_mod_four (f a) (h2 a)
  have hi (a : A) : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hs a)
  have hc : IsMulCommutative A := ⟨⟨fun a b => by
    calc
      a * b = (a * b)⁻¹ := (hi _).symm
      _ = b * a := by rw [mul_inv_rev, hi, hi]⟩⟩
  exact { toIsMulCommutative := hc
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

end HomocyclicFourTorsion

open Subgroup

namespace Subgroup

/-- The centralizer of the omega four acts elementarily on a homocyclic base,
provided its action on four-torsion has exactly the base as kernel. -/
public theorem centralizer_conj_image_elementary_of_four_torsion_faithful
    {P : Type*} [Group P] [Finite P]
    (W D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (hfaith : ∀ g ∈ centralizer (W : Set P),
      (∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) g d = d) → g ∈ D) :
    IsElementaryAbelian 2
      (((MulAut.conjNormal : P →* MulAut D).comp (centralizer (W : Set P)).subtype).range) := by
  let C := centralizer (W : Set P)
  let f := (MulAut.conjNormal : P →* MulAut D).comp C.subtype
  apply HomocyclicFourTorsion.elementary_of_homocyclic_four_torsion n hn e f.range
  · rintro a ⟨g, rfl⟩ d hd
    have hdW : (d : P) ∈ W := by
      rw [← hO]
      refine ⟨d, subset_closure ?_, rfl⟩
      simpa using hd
    apply Subtype.ext
    change (g : P) * (d : P) * (g : P)⁻¹ = d
    rw [(g.property d hdW).symm, mul_inv_cancel_right]
  · rintro a ⟨g, rfl⟩ hg
    have hgD : (g : P) ∈ D := hfaith g g.property hg
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    change (g : P) * (d : P) * (g : P)⁻¹ = d
    rw [(D.le_centralizer hgD d d.property).symm, mul_inv_cancel_right]

/-- Under faithfulness on four-torsion, an elementary sixteen supplies every
coset of the homocyclic base in the centralizer of its omega four. -/
public theorem centralizer_eq_sup_of_homocyclic_four_torsion_faithful
    {P : Type*} [Group P] [Finite P]
    (W D B : Subgroup P) [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hW : Nat.card W = 4) (hB : Nat.card B = 16) (hWB : W ≤ B) (hWD : W ≤ D)
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (hfaith : ∀ g ∈ centralizer (W : Set P),
      (∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) g d = d) → g ∈ D) :
    centralizer (W : Set P) = D ⊔ B := by
  let C := centralizer (W : Set P)
  let f := (MulAut.conjNormal : P →* MulAut D)
  have hBC : B ≤ C := B.le_centralizer.trans (centralizer_le hWB)
  have hDC' : D ≤ C := D.le_centralizer.trans (centralizer_le hWD)
  have hfix : ∀ a ∈ (f.comp C.subtype).range, ∀ d : D, d ^ 2 = 1 → a d = d := by
    rintro a ⟨g, rfl⟩ d hd
    have hdW : (d : P) ∈ W := by
      rw [← hO]
      refine ⟨d, subset_closure ?_, rfl⟩
      simpa using hd
    apply Subtype.ext
    change (g : P) * (d : P) * (g : P)⁻¹ = d
    rw [(g.property d hdW).symm, mul_inv_cancel_right]
  have hf : ∀ a ∈ (f.comp C.subtype).range,
      (∀ d : D, d ^ 4 = 1 → a d = d) → a = 1 := by
    rintro a ⟨g, rfl⟩ hg
    have hgD : (g : P) ∈ D := hfaith g g.property hg
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    change (g : P) * (d : P) * (g : P)⁻¹ = d
    rw [(D.le_centralizer hgD d d.property).symm, mul_inv_cancel_right]
  let := centralizer_conj_image_elementary_of_four_torsion_faithful W D hO n hn e hfaith
  have hc : Nat.card (f.comp C.subtype).range ≤ 4 :=
    HomocyclicFourTorsion.card_le_four_of_homocyclic_elementary_four_torsion
      n hn e _ hfix hf
  have hbc : Nat.card (f.comp B.subtype).range = 4 :=
    card_conj_image_four_of_elementary_sixteen W D B hW hB hDC hO hWB
  have hr : (f.comp B.subtype).range = (f.comp C.subtype).range := by
    apply eq_of_le_of_card_ge
    · rintro a ⟨b, rfl⟩
      exact ⟨⟨b, hBC b.property⟩, rfl⟩
    · omega
  apply le_antisymm
  · intro g hg
    have hm : f g ∈ (f.comp B.subtype).range := by
      rw [hr]
      exact ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨b, hb⟩ := hm
    have hk : f (g * (b : P)⁻¹) = 1 := by
      change f (b : P) = f g at hb
      rw [map_mul, map_inv, hb, mul_inv_cancel]
    have hd : g * (b : P)⁻¹ ∈ D := by
      apply hDC
      intro d hd
      have hh := congrArg (fun a : MulAut D => (a ⟨d, hd⟩ : P)) hk
      change (g * (b : P)⁻¹) * d * (g * (b : P)⁻¹)⁻¹ = d at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hm := (D ⊔ B).mul_mem ((show D ≤ D ⊔ B from le_sup_left) hd)
      ((show B ≤ D ⊔ B from le_sup_right) b.property)
    simpa using hm
  · exact sup_le hDC' hBC

/-- Under the explicit four-torsion faithfulness hypothesis, two nonidentity
elements of the omega four have different fourth-root counts in its centralizer. -/
public theorem centralizer_exists_ne_fourth_root_card_of_homocyclic_four_torsion_faithful
    {P : Type*} [Group P] [Finite P]
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D] (hWD : W ≤ D)
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (hfaith : ∀ g ∈ centralizer (W : Set P),
      (∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) g d = d) → g ∈ D) :
    ∃ x y : centralizer (W : Set P),
      (x : P) ∈ W ∧ x ≠ 1 ∧ (y : P) ∈ W ∧ y ≠ 1 ∧
      Nat.card {t : centralizer (W : Set P) // t ^ 4 = x} ≠
        Nat.card {t : centralizer (W : Set P) // t ^ 4 = y} := by
  let C := centralizer (W : Set P)
  let f := (MulAut.conjNormal : P →* MulAut D)
  let A := (f.comp B.subtype).range
  have hBC : B ≤ C := B.le_centralizer.trans (centralizer_le hWB)
  have hDC' : D ≤ C := D.le_centralizer.trans (centralizer_le hWD)
  have hcover : C = D ⊔ B :=
    centralizer_eq_sup_of_homocyclic_four_torsion_faithful
      W D B hW hB hWB hWD hDC hO n hn e hfaith
  have hmem (d : D) (hd : d ^ 2 = 1) : (d : P) ∈ W := by
    rw [← hO]
    refine ⟨d, subset_closure ?_, rfl⟩
    simpa using hd
  have hfix : ∀ a ∈ A, ∀ d : D, d ^ 2 = 1 → a d = d := by
    rintro a ⟨b, rfl⟩ d hd
    apply Subtype.ext
    change (b : P) * (d : P) * (b : P)⁻¹ = d
    rw [(hBC b.property d (hmem d hd)).symm, mul_inv_cancel_right]
  have hf : ∀ a ∈ A, (∀ d : D, d ^ 4 = 1 → a d = d) → a = 1 := by
    rintro a ⟨b, rfl⟩ hb
    have hbD : (b : P) ∈ D := hfaith b (hBC b.property) hb
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    change (b : P) * (d : P) * (b : P)⁻¹ = d
    rw [(D.le_centralizer hbD d d.property).symm, mul_inv_cancel_right]
  let : IsElementaryAbelian 2 A :=
    HomocyclicFourTorsion.elementary_of_homocyclic_four_torsion n hn e A hfix hf
  have hA : Nat.card A = 4 :=
    card_conj_image_four_of_elementary_sixteen W D B hW hB hDC hO hWB
  obtain ⟨x, y, hx, hx1, hy, hy1, hxy⟩ :=
    HomocyclicFourNormProfile.exists_ne_norm_fiber_card_of_homocyclic
      n hn e A hA hfix hf
  refine ⟨⟨x, hDC' x.property⟩, ⟨y, hDC' y.property⟩, hmem x hx, ?_,
    hmem y hy, ?_, ?_⟩
  · intro h
    exact hx1 (Subtype.ext (congrArg (fun z : C => (z : P)) h))
  · intro h
    exact hy1 (Subtype.ext (congrArg (fun z : C => (z : P)) h))
  · rw [card_fourth_roots_eq_norm_fibers D B C hDC hDC' hcover x,
      card_fourth_roots_eq_norm_fibers D B C hDC hDC' hcover y]
    exact hxy

end Subgroup
