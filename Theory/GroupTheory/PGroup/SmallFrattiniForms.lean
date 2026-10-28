module

public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderFiveSquare
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupTheory.PGroup.SmallFrattiniFactor

/-!
# The binary forms in the small-Frattini branch

This file isolates the source-neutral calculation used in Lemma 12.8.8(1--2).
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 12.8.8(1–2), printed pp.851–852. The denominator is the actual Frattini subgroup.  The square and commutator
maps are the maps on literal quotient carriers; no chosen coordinates or
model isomorphism is used.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement

namespace SmallFrattini


variable {Q : Type*} [Group Q] [Finite Q]

/-! The quotient and the two marked maps. -/

noncomputable def quotientSquare (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) : Q ⧸ frattini Q → frattini Q :=
  SmallNonabelianTwoGroup.frattiniSquare htwo hphi

noncomputable def quotientPolar (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) :
    Q ⧸ frattini Q → Q ⧸ frattini Q → frattini Q :=
  SmallNonabelianTwoGroup.frattiniPolar htwo hphi

@[simp] theorem quotientSquare_apply_mk (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x : Q) :
    (quotientSquare htwo hphi (QuotientGroup.mk' (frattini Q) x) : Q) = x ^ 2 := by
  exact SmallNonabelianTwoGroup.frattiniSquare_mk htwo hphi x

theorem quotientPolar_apply_mk (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x y : Q) :
    (quotientPolar htwo hphi (QuotientGroup.mk' (frattini Q) x)
      (QuotientGroup.mk' (frattini Q) y) : Q) = ⁅x, y⁆ := by
  exact SmallNonabelianTwoGroup.frattiniPolar_mk htwo hphi x y

theorem quotientSquare_mul (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x y : Q ⧸ frattini Q) :
    quotientSquare htwo hphi (x * y) =
      quotientSquare htwo hphi x * quotientSquare htwo hphi y *
        quotientPolar htwo hphi x y := by
  exact SmallNonabelianTwoGroup.frattiniSquare_mul htwo hphi x y

theorem quotientPolar_mul_left (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x y z : Q ⧸ frattini Q) :
    quotientPolar htwo hphi (x * y) z =
      quotientPolar htwo hphi x z * quotientPolar htwo hphi y z := by
  exact SmallNonabelianTwoGroup.frattiniPolar_mul_left htwo hphi x y z

theorem quotientPolar_mul_right (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x y z : Q ⧸ frattini Q) :
    quotientPolar htwo hphi x (y * z) =
      quotientPolar htwo hphi x y * quotientPolar htwo hphi x z := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction y using QuotientGroup.induction_on with
    | H y =>
      induction z using QuotientGroup.induction_on with
      | H z =>
        apply Subtype.ext
        change (quotientPolar htwo hphi (QuotientGroup.mk' (frattini Q) x)
          (QuotientGroup.mk' (frattini Q) (y * z)) : Q) =
          (quotientPolar htwo hphi (QuotientGroup.mk' (frattini Q) x)
            (QuotientGroup.mk' (frattini Q) y) : Q) *
            (quotientPolar htwo hphi (QuotientGroup.mk' (frattini Q) x)
              (QuotientGroup.mk' (frattini Q) z) : Q)
        rw [quotientPolar_apply_mk, quotientPolar_apply_mk,
          quotientPolar_apply_mk]
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hc := Subgroup.central_of_normal_card_two (frattini Q) hphi
        have hz := Subgroup.mem_center_iff.mp
          (hc (SmallNonabelianTwoGroup.frattini_commutator_mem htwo x z))
        calc
          ⁅x, y⁆ * y * ⁅x, z⁆ * y⁻¹ =
              ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by group
          _ = ⁅x, y⁆ * ⁅x, z⁆ := by rw [hz y]; simp

theorem quotientPolar_symm (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x y : Q ⧸ frattini Q) :
    quotientPolar htwo hphi x y = quotientPolar htwo hphi y x := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction y using QuotientGroup.induction_on with
    | H y =>
      apply Subtype.ext
      change (quotientPolar htwo hphi (QuotientGroup.mk' (frattini Q) x)
          (QuotientGroup.mk' (frattini Q) y) : Q) =
        (quotientPolar htwo hphi (QuotientGroup.mk' (frattini Q) y)
          (QuotientGroup.mk' (frattini Q) x) : Q)
      rw [quotientPolar_apply_mk, quotientPolar_apply_mk]
      have hc := SmallNonabelianTwoGroup.frattini_commutator_mem htwo x y
      have hs := SmallNonabelianTwoGroup.frattini_two_square_eq_one hphi
        ⟨⁅x, y⁆, hc⟩
      have hs' : ⁅x, y⁆ ^ 2 = 1 := congrArg Subtype.val hs
      calc
        ⁅x, y⁆ = ⁅x, y⁆⁻¹ := eq_inv_of_mul_eq_one_left (by simpa only [pow_two] using hs')
        _ = ⁅y, x⁆ := commutatorElement_inv x y

theorem quotientPolar_self (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x : Q ⧸ frattini Q) :
    quotientPolar htwo hphi x x = 1 := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    apply Subtype.ext
    change (quotientPolar htwo hphi (QuotientGroup.mk' (frattini Q) x)
      (QuotientGroup.mk' (frattini Q) x) : Q) = 1
    rw [quotientPolar_apply_mk]
    exact commutatorElement_self x

/-! The radical is the image of the actual center. -/

def centerImage (Q : Type*) [Group Q] : Subgroup (Q ⧸ frattini Q) :=
  (center Q).map (QuotientGroup.mk' (frattini Q))

theorem quotientPolar_radical_eq_centerImage (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) :
    {x : Q ⧸ frattini Q | ∀ y, quotientPolar htwo hphi x y = 1} =
      (centerImage Q : Set (Q ⧸ frattini Q)) := by
  ext x
  constructor
  · intro hx
    induction x using QuotientGroup.induction_on with
    | H x =>
      apply mem_map.mpr
      refine ⟨x, ?_, rfl⟩
      apply mem_center_iff.mpr
      intro y
      have hy := hx (QuotientGroup.mk' (frattini Q) y)
      have he := congrArg Subtype.val hy
      change (quotientPolar htwo hphi (QuotientGroup.mk' (frattini Q) x)
        (QuotientGroup.mk' (frattini Q) y) : Q) = 1 at he
      rw [quotientPolar_apply_mk] at he
      exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  · rintro ⟨z, hz, rfl⟩ y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) y
    apply Subtype.ext
    rw [quotientPolar_apply_mk]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_center_iff.mp hz w).symm

/-! Automorphisms and arbitrary supplied actors preserve both maps. -/

theorem quotientSquare_invariant (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (aut : MulAut Q)
    (x : Q ⧸ frattini Q) :
    quotientSquare htwo hphi (quotientAut (frattini Q) aut x) =
      quotientSquare htwo hphi x := by
  exact SmallNonabelianTwoGroup.frattiniSquare_invariant htwo hphi aut x

theorem quotientPolar_invariant (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (aut : MulAut Q)
    (x y : Q ⧸ frattini Q) :
    quotientPolar htwo hphi (quotientAut (frattini Q) aut x)
        (quotientAut (frattini Q) aut y) =
      quotientPolar htwo hphi x y := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction y using QuotientGroup.induction_on with
    | H y =>
      apply Subtype.ext
      change (quotientPolar htwo hphi
          (quotientAut (frattini Q) aut (QuotientGroup.mk' (frattini Q) x))
          (quotientAut (frattini Q) aut (QuotientGroup.mk' (frattini Q) y)) : Q) =
        (quotientPolar htwo hphi (QuotientGroup.mk' (frattini Q) x)
          (QuotientGroup.mk' (frattini Q) y) : Q)
      rw [quotientAut_apply_mk, quotientAut_apply_mk]
      simp only [quotientPolar_apply_mk]
      rw [← map_commutatorElement]
      exact SmallNonabelianTwoGroup.frattini_two_fixed hphi aut
        ⟨⁅x, y⁆, SmallNonabelianTwoGroup.frattini_commutator_mem htwo x y⟩

theorem quotientSquare_actor_invariant (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) {A : Type*} [Group A]
    (actor : A →* MulAut Q) (a : A) (x : Q ⧸ frattini Q) :
    quotientSquare htwo hphi
        (quotientAut (frattini Q) (actor a) x) = quotientSquare htwo hphi x := by
  exact quotientSquare_invariant htwo hphi (actor a) x

theorem quotientPolar_actor_invariant (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) {A : Type*} [Group A]
    (actor : A →* MulAut Q) (a : A) (x y : Q ⧸ frattini Q) :
    quotientPolar htwo hphi (quotientAut (frattini Q) (actor a) x)
        (quotientAut (frattini Q) (actor a) y) =
      quotientPolar htwo hphi x y := by
  exact quotientPolar_invariant htwo hphi (actor a) x y

/-! The square form after passing to the actual central quotient. -/

private theorem center_square_eq_one_of_frattini_bot (htwo : IsPGroup 2 Q)
    (hcenterPhi : frattini (center Q) = ⊥) (z : center Q) : ((z : center Q) : Q) ^ 2 = 1 := by
  let : Fact (IsPGroup 2 (center Q)) := ⟨htwo.to_subgroup (center Q)⟩
  let : IsElementaryAbelian 2 (center Q) :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hcenterPhi
  have hz := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (center Q)) z
  exact congrArg Subtype.val hz

private theorem central_square_well_defined (_htwo : IsPGroup 2 Q)
    (hcenterPhi : frattini (center Q) = ⊥)
    {x y : Q} (hxy : QuotientGroup.mk' (center Q) x =
      QuotientGroup.mk' (center Q) y) : x ^ 2 = y ^ 2 := by
  have hc : x⁻¹ * y ∈ center Q := QuotientGroup.eq.mp hxy
  have hcx : Commute x (x⁻¹ * y) := mem_center_iff.mp hc x
  have hc2 : (x⁻¹ * y) ^ 2 = 1 :=
    center_square_eq_one_of_frattini_bot _htwo hcenterPhi ⟨_, hc⟩
  have hy : y = x * (x⁻¹ * y) := by group
  rw [hy, hcx.mul_pow, hc2, mul_one]

noncomputable def centralSquare (htwo : IsPGroup 2 Q)
    (hcenterPhi : frattini (center Q) = ⊥) : Q ⧸ center Q → frattini Q := by
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  exact Quotient.lift
    (fun x => ⟨x ^ 2, pth_power_mem_frattini_of_isPGroup (p := 2) x⟩)
    (by
      intro x y hxy
      apply Subtype.ext
      exact central_square_well_defined htwo hcenterPhi (Quotient.sound hxy))

@[simp] theorem centralSquare_apply_mk (htwo : IsPGroup 2 Q)
    (hcenterPhi : frattini (center Q) = ⊥) (x : Q) :
    (centralSquare htwo hcenterPhi (QuotientGroup.mk' (center Q) x) : Q) = x ^ 2 := rfl

noncomputable def centralPolar (htwo : IsPGroup 2 Q)
    (hcenterPhi : frattini (center Q) = ⊥) :
    Q ⧸ center Q → Q ⧸ center Q → frattini Q :=
  fun x y =>
    (centralSquare htwo hcenterPhi x * centralSquare htwo hcenterPhi y)⁻¹ *
      centralSquare htwo hcenterPhi (x * y)

theorem centralSquare_mul (htwo : IsPGroup 2 Q)
    (_hphi : Nat.card (frattini Q) = 2) (hcenterPhi : frattini (center Q) = ⊥)
    (x y : Q ⧸ center Q) :
    centralSquare htwo hcenterPhi (x * y) =
      centralSquare htwo hcenterPhi x * centralSquare htwo hcenterPhi y *
        centralPolar htwo hcenterPhi x y := by
  simp only [centralPolar, mul_inv_cancel_left]

theorem centralPolar_apply_mk (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (hcenterPhi : frattini (center Q) = ⊥)
    (x y : Q) :
    (centralPolar htwo hcenterPhi (QuotientGroup.mk' (center Q) x)
      (QuotientGroup.mk' (center Q) y) : Q) = ⁅x, y⁆ := by
  change ((centralSquare htwo hcenterPhi (QuotientGroup.mk' (center Q) x) : Q) *
      centralSquare htwo hcenterPhi (QuotientGroup.mk' (center Q) y))⁻¹ *
      (centralSquare htwo hcenterPhi (QuotientGroup.mk' (center Q) (x * y)) : Q) = _
  rw [centralSquare_apply_mk, centralSquare_apply_mk, centralSquare_apply_mk,
    SmallNonabelianTwoGroup.square_mul_eq_square_mul_square_mul_commutator htwo hphi]
  exact inv_mul_cancel_left _ _

theorem centralSquare_invariant (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (hcenterPhi : frattini (center Q) = ⊥)
    (aut : MulAut Q) (x : Q ⧸ center Q) :
    centralSquare htwo hcenterPhi (quotientAut (center Q) aut x) =
      centralSquare htwo hcenterPhi x := by
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  induction x using QuotientGroup.induction_on with
  | H x =>
    apply Subtype.ext
    change (centralSquare htwo hcenterPhi
        (quotientAut (center Q) aut (QuotientGroup.mk' (center Q) x)) : Q) =
      (centralSquare htwo hcenterPhi (QuotientGroup.mk' (center Q) x) : Q)
    rw [quotientAut_apply_mk]
    change ((aut x) ^ 2 : Q) = x ^ 2
    rw [← map_pow]
    exact SmallNonabelianTwoGroup.frattini_two_fixed hphi aut
      ⟨x ^ 2, pth_power_mem_frattini_of_isPGroup (p := 2) x⟩

theorem centralPolar_invariant (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (hcenterPhi : frattini (center Q) = ⊥)
    (aut : MulAut Q) (x y : Q ⧸ center Q) :
    centralPolar htwo hcenterPhi (quotientAut (center Q) aut x)
        (quotientAut (center Q) aut y) = centralPolar htwo hcenterPhi x y := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction y using QuotientGroup.induction_on with
    | H y =>
      apply Subtype.ext
      change (centralPolar htwo hcenterPhi
          (quotientAut (center Q) aut (QuotientGroup.mk' (center Q) x))
          (quotientAut (center Q) aut (QuotientGroup.mk' (center Q) y)) : Q) =
        (centralPolar htwo hcenterPhi (QuotientGroup.mk' (center Q) x)
          (QuotientGroup.mk' (center Q) y) : Q)
      rw [quotientAut_apply_mk, quotientAut_apply_mk]
      rw [centralPolar_apply_mk (hphi := hphi), centralPolar_apply_mk (hphi := hphi)]
      rw [← map_commutatorElement]
      exact SmallNonabelianTwoGroup.frattini_two_fixed hphi aut
        ⟨⁅x, y⁆, SmallNonabelianTwoGroup.frattini_commutator_mem htwo x y⟩

/-! The symplectic descent does not require an elementary center. -/

omit [Finite Q] in
private theorem commutator_eq_of_center_coset_eq {x x' y : Q}
    (h : QuotientGroup.mk' (center Q) x = QuotientGroup.mk' (center Q) x') :
    ⁅x, y⁆ = ⁅x', y⁆ := by
  have hc : x⁻¹ * x' ∈ center Q := QuotientGroup.eq.mp h
  have he : x' = x * (x⁻¹ * x') := by group
  have hone : ⁅x⁻¹ * x', y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hc y).symm
  conv_rhs => rw [he, commutatorElement_mul_left_eq_conj_mul, hone]
  simp

noncomputable def centralCommutator (htwo : IsPGroup 2 Q) :
    Q ⧸ center Q → Q ⧸ center Q → frattini Q :=
  Quotient.lift₂ (fun x y => ⟨⁅x,y⁆,
    SmallNonabelianTwoGroup.frattini_commutator_mem htwo x y⟩)
    (by
      intro x y x' y' hx hy
      apply Subtype.ext
      change ⁅x, y⁆ = ⁅x', y'⁆
      exact (commutator_eq_of_center_coset_eq (Quotient.sound hx)).trans (by
        rw [← commutatorElement_inv y x', ← commutatorElement_inv y' x']
        exact congrArg Inv.inv (commutator_eq_of_center_coset_eq (Quotient.sound hy))))

@[simp] theorem centralCommutator_apply_mk (htwo : IsPGroup 2 Q) (x y : Q) :
    (centralCommutator htwo (QuotientGroup.mk' (center Q) x)
      (QuotientGroup.mk' (center Q) y) : Q) = ⁅x,y⁆ := rfl

noncomputable def frattiniToCentral (hphi : Nat.card (frattini Q) = 2) :
    (Q ⧸ frattini Q) →* Q ⧸ center Q :=
  QuotientGroup.map _ _ (MonoidHom.id Q) (central_of_normal_card_two _ hphi)

omit [Finite Q] in
@[simp] theorem frattiniToCentral_apply_mk (hphi : Nat.card (frattini Q) = 2) (x : Q) :
    frattiniToCentral hphi (QuotientGroup.mk' (frattini Q) x) =
      QuotientGroup.mk' (center Q) x := rfl

omit [Finite Q] in
theorem frattiniToCentral_surjective (hphi : Nat.card (frattini Q) = 2) :
    Function.Surjective (frattiniToCentral hphi) := by
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center Q) x
  exact ⟨QuotientGroup.mk' (frattini Q) x, rfl⟩

theorem centralCommutator_frattiniToCentral (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x y : Q ⧸ frattini Q) :
    centralCommutator htwo (frattiniToCentral hphi x) (frattiniToCentral hphi y) =
      quotientPolar htwo hphi x y := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) y
  apply Subtype.ext
  exact (quotientPolar_apply_mk htwo hphi x y).symm

theorem centralCommutator_mul_left (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x y z : Q ⧸ center Q) :
    centralCommutator htwo (x*y) z =
      centralCommutator htwo x z * centralCommutator htwo y z := by
  obtain ⟨a, rfl⟩ := frattiniToCentral_surjective hphi x
  obtain ⟨b, rfl⟩ := frattiniToCentral_surjective hphi y
  obtain ⟨c, rfl⟩ := frattiniToCentral_surjective hphi z
  rw [← map_mul, centralCommutator_frattiniToCentral,
    centralCommutator_frattiniToCentral, centralCommutator_frattiniToCentral]
  exact quotientPolar_mul_left htwo hphi a b c

theorem centralCommutator_mul_right (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x y z : Q ⧸ center Q) :
    centralCommutator htwo x (y*z) =
      centralCommutator htwo x y * centralCommutator htwo x z := by
  obtain ⟨a, rfl⟩ := frattiniToCentral_surjective hphi x
  obtain ⟨b, rfl⟩ := frattiniToCentral_surjective hphi y
  obtain ⟨c, rfl⟩ := frattiniToCentral_surjective hphi z
  rw [← map_mul, centralCommutator_frattiniToCentral,
    centralCommutator_frattiniToCentral, centralCommutator_frattiniToCentral]
  exact quotientPolar_mul_right htwo hphi a b c

theorem centralCommutator_symm (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x y : Q ⧸ center Q) :
    centralCommutator htwo x y = centralCommutator htwo y x := by
  obtain ⟨a, rfl⟩ := frattiniToCentral_surjective hphi x
  obtain ⟨b, rfl⟩ := frattiniToCentral_surjective hphi y
  rw [centralCommutator_frattiniToCentral, centralCommutator_frattiniToCentral]
  exact quotientPolar_symm htwo hphi a b

theorem centralCommutator_self (htwo : IsPGroup 2 Q) (x : Q ⧸ center Q) :
    centralCommutator htwo x x = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center Q) x
  apply Subtype.ext
  exact commutatorElement_self x

theorem centralCommutator_nondegenerate (htwo : IsPGroup 2 Q)
    (x : Q ⧸ center Q) (hx : ∀ y, centralCommutator htwo x y = 1) : x = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center Q) x
  apply (QuotientGroup.eq_one_iff _).mpr
  apply mem_center_iff.mpr
  intro y
  have hxy := congrArg Subtype.val (hx (QuotientGroup.mk' (center Q) y))
  exact (commutatorElement_eq_one_iff_mul_comm.mp hxy).symm

theorem centralCommutator_invariant (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (aut : MulAut Q) (x y : Q ⧸ center Q) :
    centralCommutator htwo (quotientAut (center Q) aut x)
      (quotientAut (center Q) aut y) = centralCommutator htwo x y := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center Q) x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center Q) y
  rw [quotientAut_apply_mk, quotientAut_apply_mk]
  apply Subtype.ext
  rw [centralCommutator_apply_mk, centralCommutator_apply_mk, ← map_commutatorElement]
  exact SmallNonabelianTwoGroup.frattini_two_fixed hphi aut
    ⟨⁅x,y⁆, SmallNonabelianTwoGroup.frattini_commutator_mem htwo x y⟩

theorem centralPolar_eq_centralCommutator (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (hcenterPhi : frattini (center Q) = ⊥)
    (x y : Q ⧸ center Q) :
    centralPolar htwo hcenterPhi x y = centralCommutator htwo x y := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center Q) x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center Q) y
  apply Subtype.ext
  exact centralPolar_apply_mk htwo hphi hcenterPhi x y


end SmallFrattini
