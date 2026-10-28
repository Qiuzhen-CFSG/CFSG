module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.IntervalCases

/-!
# Fusion through the quotient of an involution centralizer

Let `z` be an involution of a group and let `N = C_G(z)`. If two elements
of `N` have square `z` and are conjugate in the ambient group, their images
are conjugate in the actual quotient `N/⟨z⟩`. Neither image is conjugate
to the image of an element whose square is one. No finiteness or Sylow
hypothesis is needed for this transfer.

An ambient conjugator between elements with the same specified power fixes
that power, so belongs to its centralizer. For nonfusion, lift a hypothetical
quotient conjugator. Its conjugation equation holds upstairs up to a factor
in `⟨z⟩ = {1,z}`. Multiplying an element of square one by the central
involution still gives square one, contrary to the first element's square.
The final theorem combines these two arguments using the supplied quotient
subgroup and its equality with the actual cyclic subgroup; it does not
replace the quotient map by an abstract isomorphism.

This is the elementary transfer in Alperin--Brauer--Gorenstein, printed p.90
of `refs/files/alperin-brauer-gorenstein.pdf`. The ambient order-four fusion
used there is a separate input and is not inferred from the presentation.
-/

namespace Subgroup

/-- Equal specified powers force the ambient conjugator into their centralizer. -/
public theorem isConj_in_centralizer_of_pow_eq
    {G : Type*} [Group G] (z : G)
    (u v : centralizer ({z} : Set G)) (k : ℕ)
    (hu : (u : G) ^ k = z) (hv : (v : G) ^ k = z)
    (huv : IsConj (u : G) (v : G)) : IsConj u v := by
  obtain ⟨g, hg⟩ := isConj_iff.mp huv
  have hgz : g * z * g⁻¹ = z := by
    calc
      g * z * g⁻¹ = MulAut.conj g ((u : G) ^ k) := by rw [hu]; rfl
      _ = (MulAut.conj g (u : G)) ^ k := map_pow _ _ _
      _ = z := by change (g * (u : G) * g⁻¹) ^ k = z; rw [hg, hv]
  have hgN : g ∈ centralizer ({z} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    exact (mul_inv_eq_iff_eq_mul.mp hgz)
  exact isConj_iff.mpr ⟨⟨g, hgN⟩, Subtype.ext hg⟩

/-- In the central involution quotient, square roots of the involution cannot
fuse with images of elements whose square is one. -/
public theorem not_isConj_quotient_of_square_eq_central_involution
    {G : Type*} [Group G] (z : G) (hz : orderOf z = 2)
    (hzC : z ∈ center G) (Z : Subgroup G) [Z.Normal]
    (hZ : Z = zpowers z) (u b : G) (hu : u ^ 2 = z) (hb : b ^ 2 = 1) :
    ¬ IsConj (QuotientGroup.mk' Z u) (QuotientGroup.mk' Z b) := by
  classical
  intro hconj
  obtain ⟨gbar, hgbar⟩ := isConj_iff.mp hconj
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z gbar
  have hmem : g * u * g⁻¹ / b ∈ Z := by
    apply QuotientGroup.eq_iff_div_mem.mp
    change QuotientGroup.mk' Z (g * u * g⁻¹) = QuotientGroup.mk' Z b
    simpa only [map_mul, map_inv] using hgbar
  rw [hZ] at hmem
  have hzfin : IsOfFinOrder z := orderOf_pos_iff.mp (by omega)
  have hcases : g * u * g⁻¹ / b = 1 ∨ g * u * g⁻¹ / b = z := by
    obtain ⟨exponent, hexponent, heq⟩ := Finset.mem_image.mp
      (hzfin.mem_zpowers_iff_mem_range_orderOf.mp hmem)
    have hbound : exponent < 2 := by simpa only [Finset.mem_range, hz] using hexponent
    interval_cases exponent <;> simp_all
  have hsquare : (g * u * g⁻¹) ^ 2 = z := by
    calc
      (g * u * g⁻¹) ^ 2 = MulAut.conj g (u ^ 2) := (map_pow (MulAut.conj g) u 2).symm
      _ = g * z * g⁻¹ := by rw [hu]; rfl
      _ = z := by rw [mem_center_iff.mp hzC g]; simp [mul_assoc]
  have hzsq : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by intro heq; simp [heq] at hz
  apply hz1
  rcases hcases with hone | hgen
  · have heq : g * u * g⁻¹ = b := div_eq_one.mp hone
    simpa only [heq, hb] using hsquare.symm
  · have heq : g * u * g⁻¹ = z * b := (div_eq_iff_eq_mul).mp hgen
    have hcomm : Commute z b := (mem_center_iff.mp hzC b).symm
    rw [heq, hcomm.mul_pow, hzsq, hb, mul_one] at hsquare
    exact hsquare.symm

/-- Transfer ambient fusion of square roots and retain nonfusion with an
involution, using the actual cyclic quotient of the centralizer. -/
public theorem centralizer_involution_quotient_fusion
    {G : Type*} [Group G] (z : G) (hz : orderOf z = 2)
    (Z : Subgroup (centralizer ({z} : Set G))) [Z.Normal]
    (hZ : Z = zpowers ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩)
    (u v b : centralizer ({z} : Set G))
    (hu : (u : G) ^ 2 = z) (hv : (v : G) ^ 2 = z)
    (hb : (b : G) ^ 2 = 1) (huv : IsConj (u : G) (v : G)) :
    IsConj (QuotientGroup.mk' Z u) (QuotientGroup.mk' Z v) ∧
      ¬ IsConj (QuotientGroup.mk' Z u) (QuotientGroup.mk' Z b) := by
  refine ⟨(QuotientGroup.mk' Z).map_isConj
    (isConj_in_centralizer_of_pow_eq z u v 2 hu hv huv), ?_⟩
  let zN : centralizer ({z} : Set G) :=
    ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
  have hzN : orderOf zN = 2 := by
    rw [← orderOf_injective (centralizer ({z} : Set G)).subtype Subtype.val_injective zN]
    exact hz
  have hzC : zN ∈ center (centralizer ({z} : Set G)) := by
    exact mem_center_iff.mpr fun x =>
      Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
  exact not_isConj_quotient_of_square_eq_central_involution zN hzN hzC Z hZ u b
    (Subtype.ext hu) (Subtype.ext hb)

end Subgroup
