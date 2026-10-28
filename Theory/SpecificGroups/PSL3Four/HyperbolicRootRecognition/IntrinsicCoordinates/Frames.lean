module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.IntrinsicCoordinates.Collection
public import Theory.GroupTheory.PGroup.HyperbolicFactors
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Central coordinates and collection of the original hyperbolic frames

The two marked involutions coordinatize the actual center. Squares are central,
so the central quotient has exponent two and every cross correction is central.
Its four coefficients give the literal multiplication law of the source words.
Source: Aschbacher, *Sporadic Groups* (1994), 8.15 and 45.3, pp.242–243.
-/

public section

open Subgroup
namespace Theory.GroupTheory.HyperbolicRecognition.Intrinsic

variable {K : Type*} [Group K] (F : HyperbolicFactors K)

private theorem klein_of_card {G : Type*} [Group G] [Finite G]
    (hc : Nat.card G = 4) (hs : ∀ x : G, x ^ 2 = 1) : IsKleinFour G := by
  let : Nontrivial G := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  let : IsElementaryAbelian 2 G := {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hs x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  exact ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩

private theorem four_cases {G : Type*} [Group G] [Finite G] [IsKleinFour G]
    {x y : G} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) (w : G) :
    w = x*y ∨ w = x ∨ w = y ∨ w = 1 := by
  classical
  let := Fintype.ofFinite G
  have hm : w ∈ ({x*y,x,y,1} : Finset G) :=
    (IsKleinFour.eq_finset_univ hx hy hxy).symm ▸ Finset.mem_univ w
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hm

private theorem binary_pow_add {G : Type*} [Group G] (x : G) (hx : x ^ 2 = 1)
    (i j : Bit) : x ^ (i+j).val = x ^ i.val * x ^ j.val := by
  fin_cases i <;> fin_cases j
  · change x^0 = x^0*x^0; simp
  · change x^1 = x^0*x^1; simp
  · change x^1 = x^1*x^0; simp
  · change x^0 = x^1*x^1; simpa [pow_two] using hx.symm

noncomputable def centerHom : Multiplicative Central →* center K where
  toFun t := F.z ^ t.toAdd.1.val * F.u ^ t.toAdd.2.val
  map_one' := by simp
  map_mul' x y := by
    have hs (t : center K) : t ^ 2 = 1 := by
      let := F.center_elementary
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (center K)) t
    change F.z ^ (x.toAdd.1 + y.toAdd.1).val *
      F.u ^ (x.toAdd.2 + y.toAdd.2).val = _
    rw [binary_pow_add _ (hs _) , binary_pow_add _ (hs _)]
    change _ = (F.z ^ x.toAdd.1.val * F.u ^ x.toAdd.2.val) *
      (F.z ^ y.toAdd.1.val * F.u ^ y.toAdd.2.val)
    ac_rfl

@[simp] theorem centerHom_z : centerHom F (Multiplicative.ofAdd cz) = F.z := by
  simp [centerHom, cz, ZMod.val_one]
@[simp] theorem centerHom_u : centerHom F (Multiplicative.ofAdd cu) = F.u := by
  simp [centerHom, cu, ZMod.val_one]

variable [Finite K]

noncomputable def centerEquiv : Multiplicative Central ≃* center K := by
  have hs (t : center K) : t ^ 2 = 1 := by
    let := F.center_elementary
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (center K)) t
  let := klein_of_card F.center_card hs
  have hsurj : Function.Surjective (centerHom F) := by
    intro t
    rcases four_cases F.z_ne_one F.u_ne_one F.distinct t with rfl | rfl | rfl | rfl
    · exact ⟨Multiplicative.ofAdd czu, by simp [centerHom, czu, ZMod.val_one]⟩
    · exact ⟨Multiplicative.ofAdd cz, centerHom_z F⟩
    · exact ⟨Multiplicative.ofAdd cu, centerHom_u F⟩
    · exact ⟨1, map_one _⟩
  exact MulEquiv.ofBijective (centerHom F)
    ((Nat.bijective_iff_surjective_and_card _).mpr ⟨hsurj, by
      rw [F.center_card]; change Nat.card Central = 4; simp [Central, Bit]⟩)

@[simp] theorem centerEquiv_z : centerEquiv F (Multiplicative.ofAdd cz) = F.z :=
  centerHom_z F
@[simp] theorem centerEquiv_u : centerEquiv F (Multiplicative.ofAdd cu) = F.u :=
  centerHom_u F


omit [Finite K] in
private theorem correction_mem_center (F : HyperbolicFactors K) (x y : K) :
    (x*y)⁻¹*(y*x) ∈ center K := by
  let q := QuotientGroup.mk' (center K)
  have hs (w : K ⧸ center K) : w^2 = 1 := by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (center K) w
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (F.square_central w)
  have hc := Commute.of_orderOf_dvd_two
    (fun w => orderOf_dvd_of_pow_eq_one (hs w)) (q x) (q y)
  apply (QuotientGroup.eq_one_iff _).mp
  change q ((x*y)⁻¹*(y*x)) = 1
  rw [map_mul, map_inv, map_mul, map_mul, hc.eq, inv_mul_cancel]

/-- Coordinates of the correction for collecting `y*x` into `x*y`. -/
noncomputable def crossCoefficient (x y : K) : Central :=
  ((centerEquiv F).symm ⟨(x*y)⁻¹*(y*x), correction_mem_center F x y⟩).toAdd

/-- The actual four cross coefficients of four chosen lifts. -/
noncomputable def crossMatrix (a b c d : K) : Cross :=
  ⟨crossCoefficient F a c, crossCoefficient F a d,
    crossCoefficient F b c, crossCoefficient F b d⟩

theorem crossCoefficient_swap (x y : K) :
    y*x = x*y*centralEval (centerEquiv F).toMonoidHom (crossCoefficient F x y) := by
  have he : centralEval (centerEquiv F).toMonoidHom (crossCoefficient F x y) =
      (x*y)⁻¹*(y*x) :=
    congrArg Subtype.val ((centerEquiv F).apply_symm_apply _)
  rw [he, ← mul_assoc, mul_inv_cancel, one_mul]


/-- The supplied involution frames satisfy the hyperbolic collection relations. -/
theorem factorCollectionRelations (P : HyperbolicFrame F.A F.z)
    (Q : HyperbolicFrame F.B F.u) :
    CollectionRelations (centerEquiv F).toMonoidHom
      (crossMatrix F P.a P.b Q.a Q.b) P.a P.b Q.a Q.b := by
  have hz : centralEval (centerEquiv F).toMonoidHom cz = (F.z : K) :=
    congrArg Subtype.val (centerEquiv_z F)
  have hu : centralEval (centerEquiv F).toMonoidHom cu = (F.u : K) :=
    congrArg Subtype.val (centerEquiv_u F)
  exact ⟨by simpa using P.a_square, by simpa using P.b_square,
    by simpa using Q.a_square, by simpa using Q.b_square,
    hz.symm ▸ P.swap, hu.symm ▸ Q.swap,
    crossCoefficient_swap F P.a Q.a, crossCoefficient_swap F P.a Q.b,
    crossCoefficient_swap F P.b Q.a, crossCoefficient_swap F P.b Q.b⟩

end Theory.GroupTheory.HyperbolicRecognition.Intrinsic
