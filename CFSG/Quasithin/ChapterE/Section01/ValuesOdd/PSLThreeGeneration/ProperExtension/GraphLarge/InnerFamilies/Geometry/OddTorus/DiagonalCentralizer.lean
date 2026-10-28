module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.OddTorus.Control
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.OddTorus.MatrixTorus
public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension.GraphLargeStructure.Action

/-!
# Diagonal control of the coordinate four-group centralizer

A two-subgroup of the actual inner-and-graph extension centralizing the
coordinate sign four-group has diagonal lifts. Projective commutation with
each sign involution lifts to exact commutation in SL₃, which kills all
off-diagonal entries. A two-power of an inner lift is scalar; hence its
ratio of diagonal entries has two-power order in Fˣ. When |F| is three
modulo four, this ratio is ±1. Comparing any two outer elements gives an
inner element of the same subgroup, so all outer ratios agree up to sign.

This proves the published `DiagonalTwoControl` input and applies it to
`controlled_planeTorus`, with no remaining geometric premise. The proof
works for every finite field of cardinality three modulo four, in particular
for the odd prime fields greater than three required by the source branch.

Source: Aschbacher--Smith E.1.2 and E.1.5, printed pp.209--210, and
E.1.14(7), printed p.214, via Aschbacher (1982), Lemma 4.11. This is the
coordinate centralizer calculation used to construct the torus normalized
by the full original C_T(A); the source-theorem assembly is in OddTorus.
-/

public section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry.OddTorus
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

omit [Finite F] in
private theorem projective_eq_of_inner_eq {x y : SL(3,F)}
    (h : innerSL F x = innerSL F y) :
    Matrix.PSL3.projection F x = Matrix.PSL3.projection F y := by
  apply (innerPartEquiv F).injective
  apply Subtype.ext
  apply Subtype.ext
  rw [innerPartEquiv_apply_coe, innerPartEquiv_apply_coe]
  exact congrArg Subtype.val h

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
private theorem graph_centralizes_coordinateFour :
    graphElement F ∈ centralizer (coordinateFour F : Set (graphExtension F)) := by
  rw [coordinateFour, centralizer_closure]
  rintro _ ⟨k, rfl⟩
  apply Subtype.ext
  change MulAut.conj (signElement (F := F) k) * graph F =
    graph F * MulAut.conj (signElement (F := F) k)
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, graph_signElement]

private theorem diagonal_of_inner_centralizes (h2 : (2 : F) ≠ 0)
    (d : SL(3,F))
    (hd : innerSL F d ∈ centralizer (coordinateFour F : Set (graphExtension F))) :
    d.val = Matrix.diagonal (fun i => d.val i i) := by
  have hc (k : Fin 3) : d * signSL k = signSL k * d := by
    apply Matrix.PSL3.OddInvolutionFixed.commutes_of_projective_commutes _ _ (signSL_sq k)
    rw [← map_mul, ← map_mul]
    apply projective_eq_of_inner_eq F
    simp only [map_mul]
    exact (hd _ (subset_closure ⟨k, rfl⟩)).symm
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · have he := congrArg (fun x : SL(3,F) => x.val i j) (hc i)
    change (d.val * (signSL (F := F) i).val) i j =
      ((signSL (F := F) i).val * d.val) i j at he
    simp [signSL, Matrix.mul_diagonal, Matrix.diagonal_mul, Ne.symm hij] at he
    have hz : (2 : F) * d.val i j = 0 := by linear_combination -he
    rw [Matrix.diagonal_apply_ne _ hij]
    exact (mul_eq_zero.mp hz).resolve_left h2

omit [IsSimpleGroup PSL(3,F)] in
private theorem eq_one_or_graph {c : MulAut PSL(3,F)}
    (hc : c ∈ zpowers (graph F)) : c = 1 ∨ c = graph F := by
  obtain ⟨n, rfl⟩ := (isOfFinOrder_of_finite (graph F)).mem_powers_iff_mem_zpowers.mpr hc
  clear hc
  induction n with
  | zero => exact Or.inl (pow_zero _)
  | succ n ih =>
    change graph F ^ n = 1 ∨ graph F ^ n = graph F at ih
    change graph F ^ (n + 1) = 1 ∨ graph F ^ (n + 1) = graph F
    rcases ih with h | h
    · exact Or.inr (by rw [pow_succ, h, one_mul])
    · exact Or.inl (by rw [pow_succ, h, ← pow_two, graph_sq])

omit [IsSimpleGroup PSL(3,F)] in
private theorem exists_inner_or_graph (g : graphExtension F) :
    ∃ d : SL(3,F), g = innerSL F d ∨ g = innerSL F d * graphElement F := by
  obtain ⟨i, hi, c, hc, he⟩ := mem_sup_of_normal_left.mp g.property
  obtain ⟨x, rfl⟩ := hi
  obtain ⟨d, rfl⟩ := Matrix.PSL3.projection_surjective F x
  refine ⟨d, ?_⟩
  rcases eq_one_or_graph F hc with rfl | rfl
  · left
    apply Subtype.ext
    change g.val = MulAut.conj (Matrix.PSL3.projection F d)
    simpa only [mul_one] using he.symm
  · right; exact Subtype.ext he.symm

private theorem exists_diagonal_lift (h2 : (2 : F) ≠ 0) (g : graphExtension F)
    (hg : g ∈ centralizer (coordinateFour F : Set (graphExtension F))) :
    ∃ d : SL(3,F), d.val = Matrix.diagonal (fun i => d.val i i) ∧
      (g = innerSL F d ∨ g = innerSL F d * graphElement F) := by
  obtain ⟨d, h | h⟩ := exists_inner_or_graph F g
  · exact ⟨d, diagonal_of_inner_centralizes F h2 d (h ▸ hg), Or.inl h⟩
  · refine ⟨d, diagonal_of_inner_centralizes F h2 d ?_, Or.inr h⟩
    have := (centralizer (coordinateFour F : Set (graphExtension F))).mul_mem hg
      ((centralizer _).inv_mem (graph_centralizes_coordinateFour F))
    simpa only [h, mul_inv_cancel_right] using this

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
private theorem diagonal_entry_ne_zero (d : SL(3,F))
    (hd : d.val = Matrix.diagonal (fun i => d.val i i)) (i : Fin 3) : d.val i i ≠ 0 := by
  have he := congrArg (fun x : SL(3,F) => x.val i i) (mul_inv_cancel d)
  change (d.val * (d⁻¹).val) i i = (1 : Matrix (Fin 3) (Fin 3) F) i i at he
  rw [Matrix.one_apply_eq] at he
  rw [hd, Matrix.diagonal_mul] at he
  exact left_ne_zero_of_mul_eq_one he

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
private theorem diagonal_pow_entry (d : SL(3,F))
    (hd : d.val = Matrix.diagonal (fun i => d.val i i)) (n : ℕ) (i : Fin 3) :
    (d ^ n).val i i = d.val i i ^ n := by
  change (d.val ^ n) i i = _
  rw [hd, Matrix.diagonal_pow]
  simp

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
private theorem unit_sq_of_two_power {p : ℕ} (hF : Nat.card F = p) (hp4 : p % 4 = 3)
    (u : Fˣ) {n : ℕ} (hu : u ^ (2 ^ n) = 1) : u ^ 2 = 1 := by
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu)
  have hdiv : 2 ^ j ∣ p - 1 := by
    simpa only [hj, Nat.card_units, hF] using orderOf_dvd_natCard u
  have hj1 : j ≤ 1 := by
    by_contra hn
    have h4 : 4 ∣ p - 1 := (show 2 ^ 2 ∣ 2 ^ j from pow_dvd_pow 2 (by omega)).trans hdiv
    have := Nat.mod_eq_zero_of_dvd h4
    omega
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [hj]
  exact (show 2 ^ j ∣ 2 ^ 1 from pow_dvd_pow 2 hj1)

omit [Finite F] in
private theorem inner_diagonal_ratio {p : ℕ} (hF : Nat.card F = p) (hp4 : p % 4 = 3)
    (D : Subgroup (graphExtension F)) (hD : IsPGroup 2 D)
    (d : SL(3,F)) (hd : d.val = Matrix.diagonal (fun i => d.val i i))
    (hm : innerSL F d ∈ D) : d.val 2 2 = d.val 1 1 ∨ d.val 2 2 = -d.val 1 1 := by
  obtain ⟨n, hn⟩ := hD ⟨innerSL F d, hm⟩
  have hinner : innerSL F (d ^ (2 ^ n)) = innerSL F 1 := by
    rw [map_pow, map_one]
    exact congrArg Subtype.val hn
  have hc : d ^ (2 ^ n) ∈ center SL(3,F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact (projective_eq_of_inner_eq F hinner).trans (map_one _)
  obtain ⟨c, _, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have h1 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 1 1) hc
  have h2 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 2 2) hc
  have hpw : d.val 2 2 ^ (2 ^ n) = d.val 1 1 ^ (2 ^ n) := by
    simpa only [Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      diagonal_pow_entry F d hd] using h2.symm.trans h1
  have hn1 := diagonal_entry_ne_zero F d hd 1
  have hn2 := diagonal_entry_ne_zero F d hd 2
  let u : Fˣ := Units.mk0 (d.val 2 2 / d.val 1 1) (div_ne_zero hn2 hn1)
  have hu : u ^ (2 ^ n) = 1 := by
    apply Units.ext
    change (d.val 2 2 / d.val 1 1) ^ (2 ^ n) = 1
    rw [div_pow, hpw, div_self (pow_ne_zero _ hn1)]
  have hs : (d.val 2 2 / d.val 1 1) ^ 2 = 1 :=
    congrArg Units.val (unit_sq_of_two_power F hF hp4 u hu)
  rcases sq_eq_one_iff.mp hs with h | h
  · left; simpa only [one_mul] using (div_eq_iff hn1).mp h
  · right; simpa only [neg_one_mul] using (div_eq_iff hn1).mp h

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
private theorem diagonal_div_entry (d e : SL(3,F))
    (hd : d.val = Matrix.diagonal (fun i => d.val i i))
    (he : e.val = Matrix.diagonal (fun i => e.val i i)) (i : Fin 3) :
    (d * e⁻¹).val i i = d.val i i / e.val i i := by
  have hinv := congrArg (fun x : SL(3,F) => x.val i i) (mul_inv_cancel e)
  change (e.val * (e⁻¹).val) i i = (1 : Matrix (Fin 3) (Fin 3) F) i i at hinv
  rw [Matrix.one_apply_eq] at hinv
  rw [he, Matrix.diagonal_mul] at hinv
  have hei : (e⁻¹).val i i = (e.val i i)⁻¹ := eq_inv_of_mul_eq_one_right hinv
  change (d.val * (e⁻¹).val) i i = _
  rw [hd, Matrix.diagonal_mul, hei, div_eq_mul_inv, Matrix.diagonal_apply_eq]

private theorem outer_diagonal_ratio {p : ℕ} (hF : Nat.card F = p) (hp4 : p % 4 = 3)
    (h2 : (2 : F) ≠ 0) (D : Subgroup (graphExtension F)) (hD : IsPGroup 2 D)
    (hC : D ≤ centralizer (coordinateFour F : Set (graphExtension F)))
    (d e : SL(3,F)) (hd : d.val = Matrix.diagonal (fun i => d.val i i))
    (he : e.val = Matrix.diagonal (fun i => e.val i i))
    (hdD : innerSL F d * graphElement F ∈ D)
    (heD : innerSL F e * graphElement F ∈ D) :
    d.val 2 2 = (e.val 2 2 / e.val 1 1) * d.val 1 1 ∨
      d.val 2 2 = -((e.val 2 2 / e.val 1 1) * d.val 1 1) := by
  have hm : innerSL F (d * e⁻¹) ∈ D := by
    have heq : innerSL F (d * e⁻¹) =
        (innerSL F d * graphElement F) * (innerSL F e * graphElement F)⁻¹ := by
      rw [map_mul, map_inv]
      group
    rw [heq]
    exact D.mul_mem hdD (D.inv_mem heD)
  have hdiag := diagonal_of_inner_centralizes F h2 (d * e⁻¹) (hC hm)
  have hr := inner_diagonal_ratio F hF hp4 D hD (d * e⁻¹) hdiag hm
  rw [diagonal_div_entry F d e hd he 2, diagonal_div_entry F d e hd he 1] at hr
  have he1 := diagonal_entry_ne_zero F e he 1
  have he2 := diagonal_entry_ne_zero F e he 2
  rcases hr with hr | hr
  · left
    field_simp at hr ⊢
    linear_combination hr
  · right
    field_simp at hr ⊢
    linear_combination hr

omit [IsSimpleGroup PSL(3,F)] in
private theorem two_ne_zero_of_card_mod_four {p : ℕ}
    (hF : Nat.card F = p) (hp4 : p % 4 = 3) : (2 : F) ≠ 0 := by
  let := Fintype.ofFinite F
  intro hz
  have hc : ringChar F = 2 := CharP.ringChar_of_prime_eq_zero Nat.prime_two hz
  have he := FiniteField.even_card_iff_char_two.mp hc
  rw [← Nat.card_eq_fintype_card, hF] at he
  omega

/-- Every two-subgroup centralizing the actual coordinate four-group has
diagonal lifts with inner ratios ±1 and a single outer ratio up to sign. -/
theorem diagonalTwoControl {p : ℕ} (hF : Nat.card F = p) (hp4 : p % 4 = 3) :
    DiagonalTwoControl F := by
  classical
  intro D hD hC
  have h2 := two_ne_zero_of_card_mod_four F hF hp4
  by_cases ho : ∃ e : SL(3,F),
      e.val = Matrix.diagonal (fun i => e.val i i) ∧ innerSL F e * graphElement F ∈ D
  · obtain ⟨e, he, heD⟩ := ho
    let δ : Fˣ := Units.mk0 (e.val 2 2 / e.val 1 1)
      (div_ne_zero (diagonal_entry_ne_zero F e he 2) (diagonal_entry_ne_zero F e he 1))
    refine ⟨δ, ?_⟩
    intro g hg
    obtain ⟨d, hd, h | h⟩ := exists_diagonal_lift F h2 g (hC hg)
    · exact ⟨d, hd, Or.inl ⟨h, inner_diagonal_ratio F hF hp4 D hD d hd (h ▸ hg)⟩⟩
    · exact ⟨d, hd, Or.inr ⟨h, outer_diagonal_ratio F hF hp4 h2 D hD hC
        d e hd he (h ▸ hg) heD⟩⟩
  · refine ⟨1, ?_⟩
    intro g hg
    obtain ⟨d, hd, h | h⟩ := exists_diagonal_lift F h2 g (hC hg)
    · exact ⟨d, hd, Or.inl ⟨h, inner_diagonal_ratio F hF hp4 D hD d hd (h ▸ hg)⟩⟩
    · exact (ho ⟨d, hd, h ▸ hg⟩).elim

/-- The literal two-subgroup centralizer hypotheses suffice to choose one
split plane torus on which every element acts trivially or by inversion. -/
theorem centralizing_twoSubgroup_planeTorus {p : ℕ}
    (hF : Nat.card F = p) (hp4 : p % 4 = 3)
    (D : Subgroup (graphExtension F)) (hD : IsPGroup 2 D)
    (hC : D ≤ centralizer (coordinateFour F : Set (graphExtension F))) :
    ∃ (h2 : (2 : F) ≠ 0) (k : Fˣ), ∀ u : Fˣ, ∀ g ∈ D,
      g * innerSL F (planeTorus F h2 k u) * g⁻¹ = innerSL F (planeTorus F h2 k u) ∨
      g * innerSL F (planeTorus F h2 k u) * g⁻¹ = innerSL F (planeTorus F h2 k u)⁻¹ := by
  have h2 := two_ne_zero_of_card_mod_four F hF hp4
  exact ⟨h2, controlled_planeTorus F hF hp4 h2 D (diagonalTwoControl F hF hp4 D hD hC)⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry.OddTorus
