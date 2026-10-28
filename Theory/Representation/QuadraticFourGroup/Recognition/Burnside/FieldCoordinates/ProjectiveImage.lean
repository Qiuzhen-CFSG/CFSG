module

public import Theory.Representation.QuadraticFourGroup.Recognition.Burnside.FieldCoordinates.Additive
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.CharP.Two

/-!
# The projective image of the actual Sylow action

Compatible additive and scalar coordinates determine the full action on the
projective line. We normalize an involution swapping the marked Sylow subgroups
to fix coordinate one. Since it inverts their two-point stabilizer, it acts as
reciprocal on every nonzero coordinate, and interchanges zero and infinity.

A six-factor word in translations and reciprocal gives dilation by a square.
Frobenius is surjective in a finite field of characteristic two, so all scalar
actions belong to the generated projective group. The point stabilizer acts by
affine maps; a root element followed by the swap reduces every remaining group
element to that stabilizer. Thus the coordinates use exactly the transported
conjugation action on the actual Sylow set.

The final theorem is conditional on `ScalarCoordinates`. Constructing those
scalars is a separate field-theoretic step, owned by `FieldCoordinates`.

Source: W. Burnside, *On a Class of Groups of Finite Order* (1900),
pp. 274–275, `refs/original/burnside-1900.pdf`.
-/

@[expose] public section

open Subgroup
open scoped CharTwo
namespace Representation.QuadraticFourGroup.Burnside
section DilationWords

variable {K : Type*} [Field K] [CharP K 2]

private noncomputable def dilation (a : Kˣ) : Equiv.Perm (Option K) :=
  (Equiv.mulLeft₀ (a : K) a.ne_zero).optionCongr

private theorem dilation_word (a : K) (ha : a ≠ 0) :
    translation K a * reciprocal K * translation K a⁻¹ * reciprocal K *
      translation K a * reciprocal K = dilation (Units.mk0 (a ^ 2) (pow_ne_zero _ ha)) := by
  apply Equiv.ext
  rintro (_ | x)
  · simp [Equiv.Perm.mul_apply, reciprocal_some K ha, dilation]
  · by_cases hx : x = 0
    · subst x
      simp [Equiv.Perm.mul_apply, reciprocal_some K (inv_ne_zero ha), dilation]
    · by_cases hh : a + x⁻¹ = 0
      · have hax : a = x⁻¹ := CharTwo.add_eq_zero.mp hh
        have hxa : x = a⁻¹ := by rw [hax, inv_inv]
        subst x
        simp [Equiv.Perm.mul_apply, reciprocal_some K (inv_ne_zero ha),
          dilation, pow_two, ha]
      · have hi : a⁻¹ + (a + x⁻¹)⁻¹ ≠ 0 := by
          intro he
          have he' := inv_injective (CharTwo.add_eq_zero.mp he)
          have hz : x⁻¹ = 0 := add_left_cancel (he'.symm.trans (add_zero a).symm)
          exact hx (inv_eq_zero.mp hz)
        simp only [Equiv.Perm.mul_apply, reciprocal_some K hx, translation_some,
          reciprocal_some K hh, reciprocal_some K hi]
        change some (a + (a⁻¹ + (a + x⁻¹)⁻¹)⁻¹) = some (a ^ 2 * x)
        congr 1
        have hf : a + x⁻¹ = (a * x + 1) * x⁻¹ := by
          field_simp
        have hden : a * x + 1 ≠ 0 := by
          intro hz
          exact hh (by rw [hf, hz, zero_mul])
        rw [hf, mul_inv_rev, inv_inv]
        have he : a⁻¹ + x * (a * x + 1)⁻¹ = (a * (a * x + 1))⁻¹ := by
          field_simp
          ring_nf
          simp
        rw [he, inv_inv]
        ring_nf
        simp

private theorem dilation_mem [Finite K] (a : Kˣ) : dilation a ∈ projectiveGroup K := by
  obtain ⟨b, hb⟩ := Finite.surjective_of_injective (frobenius_inj K 2) (a : K)
  change b ^ 2 = (a : K) at hb
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hb
    exact a.ne_zero hb.symm
  have ha : Units.mk0 (b ^ 2) (pow_ne_zero _ hb0) = a := Units.ext hb
  rw [← ha, ← dilation_word b hb0]
  have ht (c : K) : translation K c ∈ projectiveGroup K :=
    subset_closure (Or.inl ⟨c, rfl⟩)
  have hr : reciprocal K ∈ projectiveGroup K := subset_closure (Or.inr rfl)
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (ht b) hr) (ht b⁻¹)) hr) (ht b)) hr

end DilationWords

open Theory.GroupTheory Theory.GroupTheory.InvolutionOddSpectrum
variable {G K : Type*} [Group G] [Finite G] [IsSimpleGroup G] [Group.IsPerfect G]
  [Field K]

private theorem exists_normalized_swap (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q)
    (C : ScalarCoordinates P Q K) :
    ∃ w : G, orderOf w = 2 ∧ w • P = Q ∧ w • Q = P ∧
      sylowActionInCoordinates (rootPointEquiv hG t ht P Q hPQ C.additive) w (some 1) = some 1 := by
  let ep := rootPointEquiv hG t ht P Q hPQ C.additive
  let R := ep.symm (some 1)
  have heR : ep R = some 1 := ep.apply_symm_apply _
  have hRP : R ≠ P := by
    intro he
    have hh := heR
    rw [he] at hh
    simp [ep] at hh
  have hRQ : R ≠ Q := by
    intro he
    have hh := heR
    rw [he] at hh
    simp [ep] at hh
  obtain ⟨s, hs, hsP, hsQ⟩ := hG.exists_twoPoint_swap t ht P Q hPQ
  have hsRP : s • R ≠ P := by
    intro he
    exact hRQ (smul_left_cancel s (he.trans hsQ.symm))
  have hsRQ : s • R ≠ Q := by
    intro he
    exact hRP (smul_left_cancel s (he.trans hsP.symm))
  obtain ⟨d, hd, _⟩ := hG.twoPoint_regular t ht P Q hPQ (s • R) R hsRP hsRQ hRP hRQ
  have hdFix := (mem_twoPoint P Q (d : G)).mp d.property
  let w : G := (d : G) * s
  have hwP : w • P = Q := by rw [show w = (d : G) * s from rfl, mul_smul, hsP, hdFix.2]
  have hwQ : w • Q = P := by rw [show w = (d : G) * s from rfl, mul_smul, hsQ, hdFix.1]
  have hss : s * s = 1 := by simpa [pow_two, hs] using pow_orderOf_eq_one s
  have hsd := (hG.twoPoint_swap_structure P Q hPQ s hs hsP hsQ).2 d
  have hww : w ^ 2 = 1 := by
    calc
      w ^ 2 = (d : G) * (s * (d : G) * s⁻¹) * (s * s) := by dsimp [w]; rw [pow_two]; group
      _ = 1 := by rw [hsd, hss]; simp
  have hw1 : w ≠ 1 := by
    intro he
    rw [he, one_smul] at hwP
    exact hPQ hwP
  refine ⟨w, orderOf_eq_prime hww hw1, hwP, hwQ, ?_⟩
  change ep (w • R) = some 1
  rw [show w • R = R from (mul_smul (d : G) s R).trans hd]
  exact heR

private theorem rootPointEquiv_reciprocal_mem (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q)
    (C : ScalarCoordinates P Q K) :
    reciprocal K ∈ (sylowActionInCoordinates (rootPointEquiv hG t ht P Q hPQ C.additive)).range := by
  let ep := rootPointEquiv hG t ht P Q hPQ C.additive
  let ρ := sylowActionInCoordinates ep
  have heP : ep P = none := rootPointEquiv_infinity hG t ht P Q hPQ C.additive
  have heQ : ep Q = some 0 := rootPointEquiv_zero hG t ht P Q hPQ C.additive
  have happ (g : G) (R : Sylow 2 G) : ρ g (ep R) = ep (g • R) := by
    change ep (g • ep.symm (ep R)) = _
    rw [ep.symm_apply_apply]
  obtain ⟨w, hw, hwP, hwQ, hw1⟩ := exists_normalized_swap hG t ht P Q hPQ C
  have hinv := (hG.twoPoint_swap_structure P Q hPQ w hw hwP hwQ).2
  refine ⟨w, ?_⟩
  apply Equiv.ext
  rintro (_ | x)
  · change ρ w none = some 0
    rw [← heP, happ, hwP, heQ]
  · by_cases hx : x = 0
    · subst x
      change ρ w (some 0) = reciprocal K (some 0)
      rw [← heQ, happ, hwQ, heP, heQ, reciprocal_zero]
    · let d : twoPoint P Q := C.scalars.symm (Units.mk0 x hx)
      have hdx : ρ (d : G) (some 1) = some x := by
        change sylowActionInCoordinates (rootPointEquiv hG t ht P Q hPQ C.additive)
          (d : G) (some 1) = _
        rw [rootPointEquiv_scalar]
        simp [d]
      have hdix : ρ (d : G)⁻¹ (some 1) = some x⁻¹ := by
        change sylowActionInCoordinates (rootPointEquiv hG t ht P Q hPQ C.additive)
          ((d⁻¹ : twoPoint P Q) : G) (some 1) = _
        rw [rootPointEquiv_scalar]
        simp [d]
      have hwd : w * (d : G) = (d : G)⁻¹ * w := (mul_inv_eq_iff_eq_mul).mp (hinv d)
      change ρ w (some x) = reciprocal K (some x)
      rw [← hdx, ← Equiv.Perm.mul_apply, ← map_mul, hwd, map_mul, Equiv.Perm.mul_apply]
      rw [show ρ w (some 1) = some 1 from hw1, hdix, hdx, reciprocal_some K hx]

private theorem rootPointEquiv_range_le [Finite K] [CharP K 2]
    (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q)
    (C : ScalarCoordinates P Q K) :
    (sylowActionInCoordinates (rootPointEquiv hG t ht P Q hPQ C.additive)).range ≤
      projectiveGroup K := by
  let ep := rootPointEquiv hG t ht P Q hPQ C.additive
  let ρ := sylowActionInCoordinates ep
  have hroot (x : P) : ρ (x : G) ∈ projectiveGroup K := by
    change sylowActionInCoordinates (rootPointEquiv hG t ht P Q hPQ C.additive)
      (x : G) ∈ _
    rw [rootPointEquiv_translation]
    exact subset_closure (Or.inl ⟨_, rfl⟩)
  have hscalar (d : twoPoint P Q) : ρ (d : G) ∈ projectiveGroup K := by
    have hd : ρ (d : G) = dilation (C.scalars d) := by
      apply Equiv.ext
      intro y
      exact rootPointEquiv_scalar hG t ht P Q hPQ C d y
    rw [hd]
    exact dilation_mem _
  have hstab (g : G) (hg : g • P = P) : ρ g ∈ projectiveGroup K := by
    have hgQ : g • Q ≠ P := by
      intro he
      exact hPQ (smul_left_cancel g (hg.trans he.symm))
    obtain ⟨x, hx, _⟩ := hG.sylow_regular t ht P Q (g • Q) hPQ.symm hgQ
    have hxP : (x : G) • P = P :=
      Sylow.smul_eq_iff_mem_normalizer.mpr (le_normalizer x.property)
    let d : twoPoint P Q := ⟨(x : G)⁻¹ * g, by
      apply (mem_twoPoint P Q _).mpr
      constructor
      · rw [mul_smul, hg]
        exact inv_smul_eq_iff.mpr hxP.symm
      · rw [mul_smul, ← hx, inv_smul_smul]⟩
    have heq : g = (x : G) * (d : G) := by dsimp [d]; group
    rw [heq, map_mul]
    exact mul_mem (hroot x) (hscalar d)
  obtain ⟨w, hw⟩ := rootPointEquiv_reciprocal_mem hG t ht P Q hPQ C
  have heP : ep P = none := rootPointEquiv_infinity hG t ht P Q hPQ C.additive
  have heQ : ep Q = some 0 := rootPointEquiv_zero hG t ht P Q hPQ C.additive
  have hwP : w • P = Q := by
    apply ep.injective
    calc
      ep (w • P) = ρ w (ep P) := by
        change _ = ep (w • ep.symm (ep P))
        rw [ep.symm_apply_apply]
      _ = reciprocal K none := by rw [heP]; exact congrArg (fun f => f none) hw
      _ = ep Q := heQ.symm
  have hwmem : ρ w ∈ projectiveGroup K := by
    change sylowActionInCoordinates (rootPointEquiv hG t ht P Q hPQ C.additive) w ∈ _
    rw [hw]
    exact subset_closure (Or.inr rfl)
  rintro _ ⟨g, rfl⟩
  change ρ g ∈ projectiveGroup K
  by_cases hg : g • P = P
  · exact hstab g hg
  · obtain ⟨x, hx, _⟩ := hG.sylow_regular t ht P Q (g • P) hPQ.symm hg
    have hxw : ((x : G) * w) • P = g • P := by rw [mul_smul, hwP, hx]
    have hfix : (((x : G) * w)⁻¹ * g) • P = P := by
      rw [mul_smul, ← hxw, inv_smul_smul]
    have hmem : ρ (((x : G) * w) * (((x : G) * w)⁻¹ * g)) ∈ projectiveGroup K := by
      rw [map_mul, map_mul]
      exact mul_mem (mul_mem (hroot x) hwmem) (hstab _ hfix)
    simpa only [mul_inv_cancel_left] using hmem

/-- Compatible scalar coordinates on the actual Sylow action extend to full
projective coordinates. The scalar premise is supplied by the field construction. -/
theorem nonempty_sylowCoordinates_of_scalarCoordinates
    (hG : InvolutionOddSpectrum G) (t : G) (ht : orderOf t = 2)
    (P Q : Sylow 2 G) (hPQ : P ≠ Q) {n : ℕ} (_hn : 1 < n)
    (C : ScalarCoordinates P Q (GaloisField 2 n)) :
    Nonempty (SylowCoordinates G (GaloisField 2 n)) := by
  exact ⟨{
    points := rootPointEquiv hG t ht P Q hPQ C.additive
    translations_mem := rootPointEquiv_translations_mem hG t ht P Q hPQ C.additive
    reciprocal_mem := rootPointEquiv_reciprocal_mem hG t ht P Q hPQ C
    range_le := rootPointEquiv_range_le hG t ht P Q hPQ C }⟩

end Representation.QuadraticFourGroup.Burnside

end
