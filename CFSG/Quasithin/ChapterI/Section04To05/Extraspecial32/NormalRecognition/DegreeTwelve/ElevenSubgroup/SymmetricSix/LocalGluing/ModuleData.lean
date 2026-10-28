module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.Contracts

/-!
# Cubic four-groups in the local symmetric-six calculation

The source's moved group is the literal commutator `[A(r),X]`, and its fixed
line is its intersection with `C_G(q)`. `CubicFourData` records elementary
module facts, without asserting their existence. From those facts, the cubic
norm vanishes and one nonzero vector with its cubic conjugate generates the
moved four. These calculations supply the braid and generation arguments in
`LocalGluing`.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.6, pp.40–41.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.LocalGluing

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G]

@[expose] public def movedFour (r : G) (X : Subgroup G) : Subgroup G :=
  ⁅fusionCore r, X⁆

@[expose] public def fixedLine (r q : G) (X : Subgroup G) : Subgroup G :=
  movedFour r X ⊓ centralizer ({q} : Set G)

/-- The elementary eight and the actual cubic/involution action. These
hypotheses are supplied at both ends of the source chain by `Transport`.
The moved four and its fixed line have not yet been calculated. -/
public structure CubicEightContext (r q : G) (X : Subgroup G) : Prop where
  elementary : IsElementaryAbelian 2 (fusionCore r)
  card : Nat.card (fusionCore r) = 8
  base_mem : r ∈ fusionCore r
  base_order : orderOf r = 2
  cubic_card : Nat.card X = 3
  cubic_normalizes : X ≤ normalizer (fusionCore r : Set G)
  cubic_fixed : fusionCore r ⊓ centralizer (X : Set G) = zpowers r
  involution_order : orderOf q = 2
  involution_normalizes : q ∈ normalizer (fusionCore r : Set G)
  inverts : ∀ x ∈ X, q * x * q⁻¹ = x⁻¹

/-- The actual cubic module and its involution-fixed line. There is no braid,
reflection-generation, or symmetric-group recognition assertion in this data. -/
public structure CubicFourData (r q : G) (X : Subgroup G) : Prop where
  elementary : IsElementaryAbelian 2 (movedFour r X)
  card : Nat.card (movedFour r X) = 4
  normalizes : X ≤ normalizer (movedFour r X : Set G)
  fixed_free : movedFour r X ⊓ centralizer (X : Set G) = ⊥
  decomposition : zpowers r ⊔ movedFour r X = fusionCore r
  line_card : Nat.card (fixedLine r q X) = 2

variable {r q x b : G} {X : Subgroup G}

public theorem CubicFourData.moved_le (p : CubicFourData r q X) :
    movedFour r X ≤ fusionCore r := p.decomposition ▸ le_sup_right

public theorem CubicFourData.square (p : CubicFourData r q X)
    (hb : b ∈ movedFour r X) : b * b = 1 := by
  let := p.elementary
  simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb

public theorem CubicFourData.commutes_base (p : CubicFourData r q X)
    (hb : b ∈ movedFour r X) : Commute b r :=
  mem_centralizer_singleton_iff.mp (coreInG_le r (fusionCore_le r (p.moved_le hb)))

private theorem CubicFourData.commutes (p : CubicFourData r q X)
    {b t : G} (hb : b ∈ movedFour r X) (ht : t ∈ movedFour r X) : Commute b t := by
  let := p.elementary
  exact congrArg Subtype.val (mul_comm (⟨b, hb⟩ : movedFour r X) ⟨t, ht⟩)

private theorem CubicFourData.conjugate_ne (p : CubicFourData r q X)
    (hx : zpowers x = X) (hb : b ∈ movedFour r X) (hb1 : b ≠ 1) :
    x * b * x⁻¹ ≠ b := by
  intro he
  have hbx : Commute b x := (mul_inv_eq_iff_eq_mul.mp he).symm
  have hbC : b ∈ centralizer (X : Set G) := by
    rw [← hx]
    rintro t ⟨n, rfl⟩
    exact (hbx.zpow_right n).eq.symm
  have hb0 : b ∈ (⊥ : Subgroup G) := p.fixed_free ▸ ⟨hb, hbC⟩
  exact hb1 hb0

/-- A nonzero vector and its cubic conjugate span the literal moved four. -/
public theorem CubicFourData.generated_pair [Finite G] (p : CubicFourData r q X)
    (hx : zpowers x = X) (hb : b ∈ movedFour r X) (hb1 : b ≠ 1) :
    closure ({b, x * b * x⁻¹} : Set G) = movedFour r X := by
  have hxX : x ∈ X := hx ▸ mem_zpowers x
  have ht : x * b * x⁻¹ ∈ movedFour r X := (p.normalizes hxX b).mp hb
  have ht1 : x * b * x⁻¹ ≠ 1 := by
    exact fun he => hb1 ((MulAut.conj x).map_eq_one_iff.mp he)
  have hp := isKleinFour_closure_pair b (x * b * x⁻¹)
    (p.square hb) (p.square ht) hb1 ht1 (p.conjugate_ne hx hb hb1).symm
    (p.commutes hb ht)
  apply eq_of_le_of_card_ge
  · apply (closure_le _).mpr
    intro t ht'
    rcases ht' with (rfl | rfl)
    · exact hb
    · exact ht
  · rw [p.card, hp.card_four]

/-- The cubic norm of a vector in the moved four vanishes. -/
public theorem CubicFourData.cube (p : CubicFourData r q X)
    (hx : zpowers x = X) (hx3 : x ^ 3 = 1) (hb : b ∈ movedFour r X) :
    (b * x) ^ 3 = 1 := by
  have hxX : x ∈ X := hx ▸ mem_zpowers x
  let f : G ≃* G := MulAut.conj x
  have hf (t : G) (ht : t ∈ movedFour r X) : f t ∈ movedFour r X :=
    (p.normalizes hxX t).mp ht
  have hf3 (t : G) : f (f (f t)) = t := by
    change x * (x * (x * t * x⁻¹) * x⁻¹) * x⁻¹ = t
    calc
      _ = x ^ 3 * t * (x ^ 3)⁻¹ := by simp only [pow_succ, pow_zero]; group
      _ = t := by rw [hx3, one_mul, inv_one, mul_one]
  let n : G := b * f b * f (f b)
  have hn : n ∈ movedFour r X :=
    (movedFour r X).mul_mem ((movedFour r X).mul_mem hb (hf b hb))
      (hf (f b) (hf b hb))
  have hfn : f n = n := by
    dsimp only [n]
    rw [map_mul, map_mul, hf3]
    exact (p.commutes hb ((movedFour r X).mul_mem (hf b hb)
      (hf (f b) (hf b hb)))).eq.symm.trans (mul_assoc _ _ _).symm
  have hnC : n ∈ centralizer (X : Set G) := by
    have hnx : Commute n x := (mul_inv_eq_iff_eq_mul.mp hfn).symm
    rw [← hx]
    rintro t ⟨k, rfl⟩
    exact (hnx.zpow_right k).eq.symm
  have hn1 : n = 1 := show n ∈ (⊥ : Subgroup G) from p.fixed_free ▸ ⟨hn, hnC⟩
  calc
    (b * x) ^ 3 = n * x ^ 3 := by dsimp [n, f]; simp only [pow_succ, pow_zero]; group
    _ = 1 := by rw [hn1, hx3, one_mul]

/-- Membership of the marked base, one moved involution, and a cubic generator
forces membership of the entire fusion eight. -/
public theorem CubicFourData.fusion_le [Finite G] (p : CubicFourData r q X)
    (hx : zpowers x = X) (hb : b ∈ movedFour r X) (hb1 : b ≠ 1)
    (H : Subgroup G) (hrH : r ∈ H) (hbH : b ∈ H) (hxH : x ∈ H) :
    fusionCore r ≤ H := by
  rw [← p.decomposition]
  refine sup_le (zpowers_le.mpr hrH) ?_
  rw [← p.generated_pair hx hb hb1]
  apply (closure_le _).mpr
  rintro t (rfl | rfl)
  · exact hbH
  · exact H.mul_mem (H.mul_mem hxH hbH) (H.inv_mem hxH)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.LocalGluing
