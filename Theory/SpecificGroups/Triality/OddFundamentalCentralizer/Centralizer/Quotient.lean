module

public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.Lifts

/-!
# Lifting the fundamental centralizer through a coprime central quotient

If a central kernel has prime-to-p order, an element commuting modulo that
kernel with a p-element already commutes with it upstairs: the central
commutator has order dividing both p and the center's order. Transvection
induction extends this to SL₂ over a field of characteristic p. Applying it
to the actual triality quotient proves surjectivity on the marked centralizers.

The coprime-center premise is explicit here; the parent module derives it
from relative index and quotient faithfulness of the complementary map.
The argument does not use perfectness and therefore includes SL₂(3).
Source: the coprime centralizer passage preceding (*) in Aschbacher–Smith,
A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups

namespace Triality.Standard.OddFundamentalCentralizer
open Parabolics

/-- A central kernel of order coprime to p cannot hide the failure to commute
with an element whose p-th power is one. -/
theorem commute_of_central_quotient_of_pow
    {G H : Type*} [Group G] [Group H] [Finite G] (p : ℕ)
    (f : G →* H) (hker : f.ker ≤ Subgroup.center G)
    (hc : Nat.Coprime p (Nat.card (Subgroup.center G)))
    (x y : G) (hy : y ^ p = 1) (hxy : Commute (f x) (f y)) : Commute x y := by
  let z := x * y * x⁻¹ * y⁻¹
  have hz : z ∈ Subgroup.center G := by
    apply hker
    change f (x * y * x⁻¹ * y⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [hxy.eq]
    group
  have hzy : Commute z y := (Subgroup.mem_center_iff.mp hz y).symm
  have hzpow : z ^ p = 1 := by
    have he : z * y = MulAut.conj x y := by
      dsimp only [z, MulAut.conj_apply]
      group
    have hpow : (z * y) ^ p = 1 := by
      rw [he, ← map_pow, hy, map_one]
    simpa only [hzy.mul_pow, hy, mul_one] using hpow
  let zc : Subgroup.center G := ⟨z, hz⟩
  have hzorder : orderOf zc = 1 :=
    Nat.eq_one_of_dvd_coprimes hc
      (orderOf_dvd_of_pow_eq_one (Subtype.ext hzpow : zc ^ p = 1))
      (orderOf_dvd_natCard zc)
  have hz1 : z = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp hzorder)
  change x * y = y * x
  calc
    x * y = z * (y * x) := by dsimp only [z]; group
    _ = y * x := by rw [hz1, one_mul]

private theorem transvection_pow_char {F : Type*} [Field F] (p : ℕ) [CharP F p]
    {i j : Fin 2} (hij : i ≠ j) (t : F) :
    SpecialLinearGroup.transvection hij t ^ p = 1 := by
  have hpow (n : ℕ) : SpecialLinearGroup.transvection hij t ^ n =
      SpecialLinearGroup.transvection hij (n • t) := by
    induction n with
    | zero => simp [SpecialLinearGroup.transvection_coeff_zero]
    | succ n ih =>
      rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add, succ_nsmul]
  simpa [nsmul_eq_mul, CharP.cast_eq_zero F p,
    SpecialLinearGroup.transvection_coeff_zero] using hpow p

/-- Commutation modulo a coprime central kernel lifts on the whole pinned SL₂,
using transvections rather than perfectness. In particular q = 3 is retained. -/
theorem sl2_commute_of_central_quotient
    {F G H : Type*} [Field F] [Group G] [Group H] [Finite G]
    (p : ℕ) [CharP F p] (f : G →* H) (k : SL(2, F) →* G)
    (hker : f.ker ≤ Subgroup.center G)
    (hc : Nat.Coprime p (Nat.card (Subgroup.center G))) (x : G)
    (hx : ∀ a, Commute (f (k a)) (f x)) (a : SL(2, F)) : Commute (k a) x := by
  apply Matrix.SL2.transvection_induction (fun a => Commute (k a) x) ?_ ?_ a
  · intro i j hij t
    exact (commute_of_central_quotient_of_pow p f hker hc x
      (k (SpecialLinearGroup.transvection hij t))
      (by rw [← map_pow, transvection_pow_char p, map_one]) (hx _).symm).symm
  · intro a b ha hb
    simpa only [map_mul] using ha.mul_left hb

/-- A coprime central quotient is surjective on centralizers of SL₂ images. -/
theorem exists_centralizer_lift_of_coprime
    {F G H : Type*} [Field F] [Group G] [Group H] [Finite G]
    (p : ℕ) [CharP F p] (f : G →* H) (k : SL(2, F) →* G)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center G)
    (hc : Nat.Coprime p (Nat.card (Subgroup.center G)))
    (x : H) (hx : x ∈ Subgroup.centralizer ((f.comp k).range : Set H)) :
    ∃ y : G, y ∈ Subgroup.centralizer (k.range : Set G) ∧ f y = x := by
  obtain ⟨y, hy⟩ := hf x
  refine ⟨y, ?_, hy⟩
  change ∀ a : G, a ∈ k.range → a * y = y * a
  rintro _ ⟨a, rfl⟩
  apply sl2_commute_of_central_quotient p f k hker hc y ?_ a
  intro b
  have hb : f (k b) * x = x * f (k b) :=
    Subgroup.mem_centralizer_iff.mp hx _ ⟨b, rfl⟩
  change f (k b) * f y = f y * f (k b)
  rw [hy]
  exact hb

variable {P : Parameters} (D : PinnedRankOneMaps P)

/-- Every element of the actual quotient centralizer has an elementary lift
centralizing the marked central root group when the elementary center has
prime-to-p order. No simplicity, order formula, or q > 3 premise is used. -/
theorem centralizerQuotient_surjective
    (hc : Nat.Coprime P.prime (Nat.card (Subgroup.center (ElementaryGroup P)))) :
    Function.Surjective (centralizerQuotient D) := by
  intro x
  have hker : (toCarrier P).ker ≤ Subgroup.center (ElementaryGroup P) := by
    intro z hz
    exact (toCarrier_eq_one P z).mp hz
  have he : ((toCarrier P).comp (fundamentalLift D)).range = fundamental P :=
    range_fundamentalHom D
  have hx : x.val ∈ Subgroup.centralizer
      (((toCarrier P).comp (fundamentalLift D)).range : Set (Carrier P)) :=
    (congrArg (fun K : Subgroup (Carrier P) =>
      x.val ∈ Subgroup.centralizer (K : Set (Carrier P))) he).mpr x.property
  have hfin : Finite (ElementaryGroup P) := inferInstance
  have hchar : CharP (GaloisField P.prime P.exponent) P.prime := inferInstance
  -- Elaborate the field and subgroup instances before applying the quotient data.
  have hlift := exists_centralizer_lift_of_coprime
    (F := GaloisField P.prime P.exponent) (G := ElementaryGroup P) (H := Carrier P)
    P.prime (toCarrier P) (fundamentalLift D)
  have hxLift := hlift (toCarrier_surjective P) hker hc x.val
  have hex := hxLift hx
  obtain ⟨y, hmem, hy⟩ := hex
  exact ⟨⟨y, hmem⟩, Subtype.ext hy⟩

end Triality.Standard.OddFundamentalCentralizer
