module

public import Theory.GroupTheory.PGroup.ClassTwoSquareClasses
public import Theory.ElementaryAbelian.AnisotropicQuadratic

/-!
# Quadratic square classes on an elementary central quotient

When the central quotient is elementary binary and all involutions are central,
squaring gives an anisotropic quadratic map to the center modulo its squares.
Changing a representative changes its square by a central square. Conversely,
a central square root corrects any element in the zero fiber to an involution.
The commutator supplies the bilinear polar map.

Source: the square-map argument for groups with three involutions in
Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3 and Lemma 5.1. This version
retains central square classes instead of requiring an elementary center.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace IsPGroup

/-- Squaring modulo central squares is anisotropic and quadratic on an
elementary central quotient when involutions are central. -/
public theorem exists_anisotropic_center_quotient_square_class_map
    {G : Type*} [Group G] [IsElementaryAbelian 2 (G ⧸ center G)]
    (hcentral : ∀ x : G, x ^ 2 = 1 → x ∈ center G) :
    let S := (powMonoidHom 2 : center G →* center G).range
    ∃ (square : G ⧸ center G → center G ⧸ S)
      (polar : G ⧸ center G → G ⧸ center G → center G ⧸ S),
      (∀ (x : G) (hx : x ^ 2 ∈ center G),
        square (QuotientGroup.mk' (center G) x) = QuotientGroup.mk' S ⟨x ^ 2, hx⟩) ∧
      square 1 = 1 ∧
      (∀ x y, square (x * y) = square x * square y * polar x y) ∧
      (∀ x y z, polar (x * y) z = polar x z * polar y z) ∧
      (∀ x, square x = 1 → x = 1) := by
  let S := (powMonoidHom 2 : center G →* center G).range
  let r := QuotientGroup.mk' S
  have hsq (x : G) : x ^ 2 ∈ center G := by
    apply (QuotientGroup.eq_one_iff (N := center G) _).mp
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (G ⧸ center G))
      (QuotientGroup.mk' (center G) x)
  have hsame (x y : G)
      (hxy : QuotientGroup.mk' (center G) x = QuotientGroup.mk' (center G) y) :
      r ⟨x ^ 2, hsq x⟩ = r ⟨y ^ 2, hsq y⟩ := by
    have hm : x⁻¹ * y ∈ center G := QuotientGroup.eq.mp hxy
    have hc : Commute x (x⁻¹ * y) := mem_center_iff.mp hm x
    apply QuotientGroup.eq.mpr
    refine ⟨⟨x⁻¹ * y, hm⟩, ?_⟩
    apply Subtype.ext
    change (x⁻¹ * y) ^ 2 = (x ^ 2)⁻¹ * y ^ 2
    apply (eq_inv_mul_iff_mul_eq).mpr
    simpa only [mul_inv_cancel_left] using (hc.mul_pow 2).symm
  let square : G ⧸ center G → center G ⧸ S :=
    Quotient.lift (fun x => r ⟨x ^ 2, hsq x⟩) (by
      intro x y hxy
      exact hsame x y (Quotient.sound hxy))
  let polar (x y : G ⧸ center G) := (square x * square y)⁻¹ * square (x * y)
  have hclass : commutator G ≤ center G :=
    Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hcomm (x y : G) : ⁅x,y⁆ ∈ center G :=
    hclass (commutator_mem_commutator (mem_top x) (mem_top y))
  have hmul (x y : G) : (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅x,y⁆ := by
    symm
    calc
      x ^ 2 * y ^ 2 * ⁅x,y⁆ = ⁅x,y⁆ * (x ^ 2 * y ^ 2) :=
        mem_center_iff.mp (hcomm x y) _
      _ = x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by
        simp only [commutatorElement_def, mul_assoc]
      _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by
        rw [mem_center_iff.mp (hsq x)]
      _ = (x * y) ^ 2 := by simp only [pow_two]; group
  have hpolar (x y : G) :
      polar (QuotientGroup.mk' (center G) x) (QuotientGroup.mk' (center G) y) =
        r ⟨⁅x,y⁆, hcomm x y⟩ := by
    change (r ⟨x ^ 2, hsq x⟩ * r ⟨y ^ 2, hsq y⟩)⁻¹ * r ⟨(x*y)^2, hsq (x*y)⟩ = _
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    change (x ^ 2 * y ^ 2)⁻¹ * (x*y)^2 = ⁅x,y⁆
    rw [hmul, inv_mul_cancel_left]
  refine ⟨square, polar, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · change r ⟨(1 : G)^2, hsq 1⟩ = 1
    exact (congrArg r (Subtype.ext (one_pow 2))).trans (map_one r)
  · intro x y
    simp only [polar, mul_inv_cancel_left]
  · intro x y z
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        induction z using QuotientGroup.induction_on with
        | H z =>
          change polar (QuotientGroup.mk' (center G) (x*y))
            (QuotientGroup.mk' (center G) z) =
              polar (QuotientGroup.mk' (center G) x) (QuotientGroup.mk' (center G) z) *
              polar (QuotientGroup.mk' (center G) y) (QuotientGroup.mk' (center G) z)
          rw [hpolar, hpolar, hpolar, ← map_mul]
          congr 1
          apply Subtype.ext
          change ⁅x*y,z⁆ = ⁅x,z⁆ * ⁅y,z⁆
          rw [commutatorElement_mul_left_eq_conj_mul]
          have hc := mem_center_iff.mp (hcomm y z)
          rw [hc x]
          simp only [mul_assoc, mul_inv_cancel, mul_one]
          exact (hc ⁅x,z⁆).symm
  · intro x hx
    induction x using QuotientGroup.induction_on with
    | H x =>
      have hm : (⟨x ^ 2, hsq x⟩ : center G) ∈ S :=
        (QuotientGroup.eq_one_iff _).mp hx
      obtain ⟨z, hz⟩ := hm
      exact (QuotientGroup.eq_one_iff x).mpr
        (mem_center_of_square_eq_central_square hcentral x z
          (congrArg Subtype.val hz).symm)

/-- For a finite two-group with elementary central quotient and central
involutions, the Frattini quotient has order at most the square of the first
omega subgroup of the center. Restricting the square map to the image of
Frattini modulo central squares supplies the sharper bound. -/
public theorem card_frattini_quotient_le_sq_card_omega_center
    {G : Type*} [Group G] [Finite G] [IsElementaryAbelian 2 (G ⧸ center G)]
    (hG : IsPGroup 2 G)
    (hcentral : ∀ x : G, x ^ 2 = 1 → x ∈ center G) :
    Nat.card (G ⧸ frattini G) ≤ (Nat.card (omega₁ (center G) (p := 2))) ^ 2 := by
  let Z := center G
  let S := (powMonoidHom 2 : Z →* Z).range
  let W := Z ⧸ S
  let r : Z →* W := QuotientGroup.mk' S
  let F := (frattini G).subgroupOf Z
  let R := F.map r
  have hsq (x : G) : x ^ 2 ∈ center G := by
    apply (QuotientGroup.eq_one_iff (N := center G) _).mp
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (G ⧸ center G))
      (QuotientGroup.mk' (center G) x)
  have hphisq (x : G) : x ^ 2 ∈ frattini G := by
    rw [hG.frattini_eq_closure_squares]
    exact subset_closure ⟨x, rfl⟩
  have hphi : frattini G ≤ Z := by
    rw [hG.frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro x ⟨y, rfl⟩
    exact hsq y
  have hSF : S ≤ F := by
    rintro z ⟨a, rfl⟩
    exact hphisq a
  let : IsElementaryAbelian 2 W := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective S x
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩) }
  let : IsElementaryAbelian 2 R := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 W) (x : W)) }
  obtain ⟨square, polar, hsquare, hone, hquadratic, hbilinear, hanisotropic⟩ :=
    exists_anisotropic_center_quotient_square_class_map hcentral
  have hsquareR (x : G ⧸ center G) : square x ∈ R := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (center G) x
    rw [hsquare a (hsq a)]
    exact mem_map_of_mem r (hphisq a)
  have hpolarR (x y : G ⧸ center G) : polar x y ∈ R := by
    have he : polar x y = (square x * square y)⁻¹ * square (x*y) := by
      rw [hquadratic, inv_mul_cancel_left]
    rw [he]
    exact R.mul_mem (R.inv_mem (R.mul_mem (hsquareR x) (hsquareR y))) (hsquareR (x*y))
  let squareR (x : G ⧸ center G) : R := ⟨square x, hsquareR x⟩
  let polarR (x y : G ⧸ center G) : R := ⟨polar x y, hpolarR x y⟩
  have hbound : Nat.card (G ⧸ center G) ≤ (Nat.card R)^2 :=
    IsElementaryAbelian.card_le_sq_of_anisotropic_quadratic squareR polarR
      (Subtype.ext hone) (fun x y => Subtype.ext (hquadratic x y))
      (fun x y z => Subtype.ext (hbilinear x y z))
      (fun x hx => hanisotropic x (congrArg Subtype.val hx))
  have hRindex : R.index = F.index := by
    apply F.index_map_eq (QuotientGroup.mk'_surjective S)
    exact (QuotientGroup.ker_mk' S).le.trans hSF
  have hFmap : F.map Z.subtype = frattini G := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hphi]
  have hphiindex : (frattini G).index = F.index * Z.index := by
    rw [← hFmap, index_map_subtype]
  have hcard : Nat.card R * F.index = Nat.card W := by
    rw [← hRindex]
    exact R.card_mul_index
  have hRle : Nat.card R ≤ Nat.card W :=
    Nat.card_le_card_of_injective R.subtype R.subtype_injective
  have hW : Nat.card W = Nat.card (omega₁ (center G) (p := 2)) := by
    rw [← index_eq_card, index_range, square_ker_eq_omega_one]
  calc
    Nat.card (G ⧸ frattini G) = F.index * Nat.card (G ⧸ center G) := hphiindex
    _ ≤ F.index * (Nat.card R)^2 := Nat.mul_le_mul_left _ hbound
    _ = Nat.card W * Nat.card R := by rw [← hcard]; ring
    _ ≤ Nat.card W * Nat.card W := Nat.mul_le_mul_left _ hRle
    _ = (Nat.card (omega₁ (center G) (p := 2)))^2 := by rw [hW, pow_two]

end IsPGroup
