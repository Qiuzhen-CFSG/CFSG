module

public import Theory.GroupTheory.PGroup.CriticalSubgroup
public import Theory.GroupTheory.PGroup.CentralQuotientQuadratic
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# The intrinsic order of a critical subgroup with elementary center four

Let C be a critical subgroup of a finite group P, with elementary center of
order four and all its involutions central in C. Suppose the first omega of
the ambient center has order two and P contains a subgroup of order sixteen.
Then C has order sixteen.

The critical commutator condition and the exponent-two center imply that
ambient conjugation fixes every square in C. Thus the anisotropic quadratic
square-class map on C/Z(C) takes values in an image of the ambient central
omega, of order at most two. The binary quadratic bound gives |C/Z(C)| ≤ 4.
A nontrivial cyclic central quotient is impossible. In the remaining abelian
case C is a Klein four, and critical self-centrality embeds P/C in its
automorphism group of order six. Then |P| divides 24, contradicting the
subgroup of order sixteen.

The ambient two-group hypothesis and elementary abelianness of the subgroup
of order sixteen are unnecessary for this calculation.

Source context: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, printed p.386;
Thompson's critical-subgroup theorem, Gorenstein, *Finite Groups*, Theorem
5.3.11. The quadratic dimension bound is supplied by the existing
Chevalley–Warning development.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace IsCriticalPSubgroup

/-- Ambient conjugation fixes squares in a critical subgroup whose center
has exponent two. -/
public theorem sq_mem_ambient_center_of_elementary_center
    {P : Type*} [Group P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C) [IsElementaryAbelian 2 (center C)]
    (x : C) : (x : P) ^ 2 ∈ center P := by
  apply mem_center_iff.mpr
  intro g
  obtain ⟨z, hz, he⟩ := hC.commutator_le
    (commutator_mem_commutator (mem_top g) x.property)
  have hcomm : Commute (z : P) (x : P) :=
    (congrArg Subtype.val (mem_center_iff.mp hz x)).symm
  have hz2 : (z : P) ^ 2 = 1 := congrArg Subtype.val
    (elemPow_eq_one_of_isElementaryAbelian z hz)
  have hconj : MulAut.conj g (x : P) = (z : P) * x := by
    rw [conj_eq_commutatorElement_mul, ← he]
    rfl
  have hfix : MulAut.conj g ((x : P)^2) = (x : P)^2 := by
    rw [map_pow, hconj, hcomm.mul_pow, hz2, one_mul]
  exact mul_inv_eq_iff_eq_mul.mp hfix


/-- Central involutions and an elementary critical center bound its central
quotient by four when the ambient central omega has order two. -/
public theorem card_center_quotient_le_four_of_elementary_center
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C) [IsElementaryAbelian 2 (center C)]
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hinv : ∀ x : C, x ^ 2 = 1 → x ∈ center C) :
    Nat.card (C ⧸ center C) ≤ 4 := by
  let : IsElementaryAbelian 2 (C ⧸ center C) := hC.quotient_elementary
  let D := (omega₁ (center P) (p := 2)).map (center P).subtype
  let i : center C →* P := C.subtype.comp (center C).subtype
  let A := D.comap i
  let S := (powMonoidHom 2 : center C →* center C).range
  let r := QuotientGroup.mk' S
  let R := A.map r
  have hD : Nat.card D = 2 := by
    rw [card_map_of_injective (center P).subtype_injective, hZ]
  have hi : Function.Injective i := C.subtype_injective.comp (center C).subtype_injective
  have hR : Nat.card R ≤ 2 := by
    apply Nat.le_of_dvd (by decide)
    rw [← hD]
    exact (card_map_dvd A r).trans (card_comap_dvd_of_injective D i hi)
  let : IsElementaryAbelian 2 A := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (center C)) (x : center C)) }
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.map r
  obtain ⟨square, polar, hsquare, hone, hquadratic, hbilinear, hanisotropic⟩ :=
    IsPGroup.exists_anisotropic_center_quotient_square_class_map hinv
  have hsquareR (x : C ⧸ center C) : square x ∈ R := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (center C) x
    have ha := hC.quotient_elementary.sq_mem_center_of_central_quotient a
    rw [hsquare a ha]
    apply mem_map_of_mem r
    change (a : P)^2 ∈ D
    refine ⟨⟨(a : P)^2, hC.sq_mem_ambient_center_of_elementary_center a⟩,
      subset_closure ?_, rfl⟩
    apply Subtype.ext
    simpa using congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian (a^2) ha)
  have hpolarR (x y : C ⧸ center C) : polar x y ∈ R := by
    have he : polar x y = (square x * square y)⁻¹ * square (x*y) := by
      rw [hquadratic, inv_mul_cancel_left]
    rw [he]
    exact R.mul_mem (R.inv_mem (R.mul_mem (hsquareR x) (hsquareR y))) (hsquareR (x*y))
  let squareR (x : C ⧸ center C) : R := ⟨square x, hsquareR x⟩
  let polarR (x y : C ⧸ center C) : R := ⟨polar x y, hpolarR x y⟩
  have hbound := IsElementaryAbelian.card_le_sq_of_anisotropic_quadratic squareR polarR
    (Subtype.ext hone) (fun x y => Subtype.ext (hquadratic x y))
    (fun x y z => Subtype.ext (hbilinear x y z))
    (fun x hx => hanisotropic x (congrArg Subtype.val hx))
  nlinarith


private theorem center_ne_top_of_subgroup_card_sixteen
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C) [IsElementaryAbelian 2 (center C)]
    (hCZ : Nat.card (center C) = 4)
    (B : Subgroup P) (hB : Nat.card B = 16) : center C ≠ ⊤ := by
  intro hab
  have hcardC : Nat.card C = 4 := by
    simpa only [hab, Nat.card_congr (Subgroup.topEquiv (G := C)).toEquiv] using hCZ
  let : IsElementaryAbelian 2 C := {
    toIsMulCommutative := center_eq_top_iff.mp hab
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      elemPow_eq_one_of_isElementaryAbelian x (hab ▸ mem_top x)) }
  let : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardC]; decide)
  let : IsKleinFour C := ⟨hcardC, IsElementaryAbelian.exponent_eq_prime⟩
  let : C.Characteristic := hC.characteristic
  let f : P →* MulAut C := MulAut.conjNormal
  have hker : f.ker = (center C).map C.subtype := by
    rw [← hC.centralizer_eq]
    ext x
    constructor
    · intro hx c hc
      have hh := congrArg (fun a : MulAut C => (a ⟨c, hc⟩ : P))
        (MonoidHom.mem_ker.mp hx)
      change x * c * x⁻¹ = c at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hx
      apply MonoidHom.mem_ker.mpr
      ext c
      change x * (c : P) * x⁻¹ = c
      rw [← hx c c.property, mul_inv_cancel_right]
  have hcard := f.ker.card_mul_index
  rw [index_ker, hker, card_map_of_injective C.subtype_injective, hCZ] at hcard
  have hdiv : Nat.card P ∣ 24 := by
    rw [← hcard]
    change 4 * Nat.card f.range ∣ 4 * 6
    apply Nat.mul_dvd_mul_left 4
    rw [← IsKleinFour.card_mulAut C]
    exact card_subgroup_dvd_card f.range
  have hBdiv : 16 ∣ Nat.card P := hB ▸ card_subgroup_dvd_card B
  exact (by decide : ¬ 16 ∣ 24) (hBdiv.trans hdiv)

/-- A critical subgroup with elementary center four and central involutions
has order sixteen if the ambient central omega has order two and the ambient
group contains a subgroup of order sixteen. No ambient p-group hypothesis or
elementarity hypothesis on that subgroup is needed. -/
public theorem card_eq_sixteen_of_elementary_center
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (B : Subgroup P) (hB : Nat.card B = 16)
    (hCZ : Nat.card (center C) = 4) [IsElementaryAbelian 2 (center C)]
    (hinv : ∀ x : C, x ^ 2 = 1 → x ∈ center C) : Nat.card C = 16 := by
  let : IsElementaryAbelian 2 (C ⧸ center C) := hC.quotient_elementary
  have hbound := hC.card_center_quotient_le_four_of_elementary_center hZ hinv
  have hnonab := hC.center_ne_top_of_subgroup_card_sixteen hCZ B hB
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 (C ⧸ center C)).exists_card_eq
  have hnle : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hn] using hbound
  have hquot : Nat.card (C ⧸ center C) = 4 := by
    by_contra hne
    have hd : Nat.card (C ⧸ center C) ∣ 2 := by
      rw [hn]
      interval_cases n
      · decide
      · decide
      · exact (hne hn).elim
    let : IsCyclic (C ⧸ center C) := isCyclic_of_card_dvd_prime hd
    exact hnonab (center_eq_top_iff.mpr (isMulCommutative_of_isCyclic_quotient_center_self C))
  have hcard := (center C).card_eq_card_quotient_mul_card_subgroup
  rw [hquot, hCZ] at hcard
  exact hcard

end IsCriticalPSubgroup
