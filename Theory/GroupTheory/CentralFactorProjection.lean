module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group

/-!
# Projections onto a commuting factor

A homomorphism f from U into L is a projection when u / f(u) centralizes L.
Its relative normalizer preserves U joined with the image. If U is abelian,
this join is a commuting product. Once that normalizer also preserves U,
transitivity on the nonidentity image elements forces the image into U:
a nontrivial displacement belongs to both groups, and its orbit fills the image.
This gives U = C_U(L)(U intersect L).

For a centerless L, pointwise equality of the U-action and a subgroup Q's
inner action constructs the projection itself. The proof retains actual
ambient elements and never assumes the desired splitting.

Source: the projected-factor argument in Aschbacher--Smith,
Proposition 2.2.2, printed p.520, combined manuscript of 1 March 2004.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace Subgroup.CentralFactor
variable {G : Type*} [Group G] {U L : Subgroup G}

private theorem inner_implementer_unique
    (hdis : Disjoint L (centralizer (L : Set G))) {u q r : G}
    (hq : q ∈ L) (hr : r ∈ L)
    (hcq : u * q⁻¹ ∈ centralizer (L : Set G))
    (hcr : u * r⁻¹ ∈ centralizer (L : Set G)) : q = r := by
  have hc : q * r⁻¹ ∈ centralizer (L : Set G) := by
    have h := (centralizer (L : Set G)).mul_mem
      ((centralizer (L : Set G)).inv_mem hcq) hcr
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] using h
  exact mul_inv_eq_one.mp (hdis.le_bot ⟨L.mul_mem hq (L.inv_mem hr), hc⟩)

/-- Equality of the actual inner-action images gives a surjective projection
onto Q. Trivial intersection of L with its centralizer makes implementers
unique and proves multiplicativity; no splitting of U is assumed. -/
theorem exists_projection_of_inner_implementers
    (Q : Subgroup G) (hQL : Q ≤ L)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (hinner : ∀ u : U, ∃ q : Q, (u : G) * (q : G)⁻¹ ∈ centralizer (L : Set G))
    (honto : ∀ q : Q, ∃ u : U, (u : G) * (q : G)⁻¹ ∈ centralizer (L : Set G)) :
    ∃ f : U →* G, f.range = Q ∧
      ∀ u : U, (u : G) * (f u)⁻¹ ∈ centralizer (L : Set G) := by
  classical
  choose q hq using hinner
  let f : U →* G :=
    { toFun := fun u => (q u : G)
      map_one' := inner_implementer_unique hdis (hQL (q 1).property) L.one_mem
        (hq 1) (by simp)
      map_mul' := by
        intro u v
        apply inner_implementer_unique hdis (hQL (q (u * v)).property)
          (L.mul_mem (hQL (q u).property) (hQL (q v).property)) (hq (u * v))
        have he : (u : G) * (v : G) * ((q u : G) * (q v : G))⁻¹ =
            ((u : G) * (q u : G)⁻¹) * ((v : G) * (q v : G)⁻¹) := by
          calc
            _ = (u : G) * (((v : G) * (q v : G)⁻¹) * (q u : G)⁻¹) := by group
            _ = (u : G) * ((q u : G)⁻¹ * ((v : G) * (q v : G)⁻¹)) := by
              rw [← hq v (q u : G)⁻¹ (L.inv_mem (hQL (q u).property))]
            _ = _ := by group
        change (u : G) * (v : G) * ((q u : G) * (q v : G))⁻¹ ∈ _
        rw [he]
        exact (centralizer (L : Set G)).mul_mem (hq u) (hq v) }
  refine ⟨f, le_antisymm ?_ ?_, hq⟩
  · rintro x ⟨u, rfl⟩
    exact (q u).property
  · intro x hx
    obtain ⟨u, hu⟩ := honto ⟨x, hx⟩
    exact ⟨u, inner_implementer_unique hdis (hQL (q u).property) (hQL hx) (hq u) hu⟩

/-- Conjugation by an element of L changes only the projected factor. -/
theorem projection_conjugate (f : U →* G)
    (hc : ∀ u : U, (u : G) * (f u)⁻¹ ∈ centralizer (L : Set G))
    (u : U) {n : G} (hn : n ∈ L) :
    n * (u : G) * n⁻¹ = ((u : G) * (f u)⁻¹) * (n * f u * n⁻¹) := by
  calc
    n * (u : G) * n⁻¹ = (n * ((u : G) * (f u)⁻¹)) * (f u * n⁻¹) := by group
    _ = (((u : G) * (f u)⁻¹) * n) * (f u * n⁻¹) := by rw [hc u n hn]
    _ = _ := by group

/-- The projected image of an abelian subgroup centralizes that subgroup. -/
theorem projection_range_centralizes [IsMulCommutative U]
    (f : U →* G) (hf : f.range ≤ L)
    (hc : ∀ u : U, (u : G) * (f u)⁻¹ ∈ centralizer (L : Set G)) :
    f.range ≤ centralizer (U : Set G) := by
  rintro q ⟨a, rfl⟩ u hu
  have hh := projection_conjugate f hc (⟨u, hu⟩ : U) (hf (show f a ∈ f.range from ⟨a, rfl⟩))
  have hcomm : f a * f ⟨u, hu⟩ = f ⟨u, hu⟩ * f a := by rw [← map_mul, mul_comm a, map_mul]
  rw [hcomm, mul_inv_cancel_right] at hh
  have he : f a * u * (f a)⁻¹ = u := by simpa only [inv_mul_cancel_right] using hh
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The relative normalizer of the projected image normalizes the join
of that image with U, even before the image is known to lie in U. -/
theorem projection_normalizer_le_join_normalizer
    (f : U →* G)
    (hc : ∀ u : U, (u : G) * (f u)⁻¹ ∈ centralizer (L : Set G)) :
    L ⊓ normalizer (f.range : Set G) ≤ normalizer ((U ⊔ f.range : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro n hn x hx
  have hU : U ≤ (U ⊔ f.range).comap (MulAut.conj n).toMonoidHom := by
    intro u hu
    change n * u * n⁻¹ ∈ U ⊔ f.range
    rw [projection_conjugate f hc ⟨u, hu⟩ hn.1]
    exact (U ⊔ f.range).mul_mem
      ((U ⊔ f.range).mul_mem ((le_sup_left : U ≤ U ⊔ f.range) hu)
        ((U ⊔ f.range).inv_mem ((le_sup_right : f.range ≤ U ⊔ f.range) ⟨⟨u, hu⟩, rfl⟩)))
      ((le_sup_right : f.range ≤ U ⊔ f.range) ((mem_normalizer_iff.mp hn.2 (f ⟨u, hu⟩)).mp ⟨⟨u, hu⟩, rfl⟩))
  have hQ : f.range ≤ (U ⊔ f.range).comap (MulAut.conj n).toMonoidHom := by
    intro q hq
    exact (le_sup_right : f.range ≤ U ⊔ f.range) ((mem_normalizer_iff.mp hn.2 q).mp hq)
  exact (sup_le hU hQ) hx

/-- A subgroup acting through inner implementers in L normalizes L. -/
theorem projection_le_normalizer (f : U →* G) (hf : f.range ≤ L)
    (hc : ∀ u : U, (u : G) * (f u)⁻¹ ∈ centralizer (L : Set G)) :
    U ≤ normalizer (L : Set G) := by
  intro u hu
  have hc' := centralizer_le_normalizer (L : Set G) (hc ⟨u, hu⟩)
  have hf' := L.le_normalizer (hf (show f ⟨u, hu⟩ ∈ f.range from ⟨⟨u, hu⟩, rfl⟩))
  simpa only [inv_mul_cancel_right] using (normalizer (L : Set G)).mul_mem hc' hf'

/-- If the relative normalizer preserves U and is transitive on the
nonidentity projected elements, a nontrivial projection forces the whole
image into U. The order bound excludes the diagonal order-two exception. -/
theorem projection_range_le_of_transitive [Finite G]
    (f : U →* G)
    (hc : ∀ u : U, (u : G) * (f u)⁻¹ ∈ centralizer (L : Set G))
    (hn : L ⊓ normalizer (f.range : Set G) ≤ normalizer (U : Set G))
    (hsize : 2 < Nat.card f.range)
    (htrans : ∀ a ∈ f.range, a ≠ 1 → ∀ b ∈ f.range, b ≠ 1 →
      ∃ n ∈ L ⊓ normalizer (f.range : Set G), n * a * n⁻¹ = b)
    (z : U) (hz : f z ≠ 1) : f.range ≤ U := by
  classical
  let _ : Fintype f.range := Fintype.ofFinite f.range
  have h3 : 3 ≤ ENat.card f.range := by
    rw [ENat.card_eq_coe_fintype_card]
    have hh : 3 ≤ Fintype.card f.range := by
      rw [← Nat.card_eq_fintype_card]
      omega
    exact_mod_cast hh
  obtain ⟨b, hb1, hbz⟩ := ENat.exists_ne_ne_of_three_le h3 (1 : f.range) ⟨f z, ⟨z, rfl⟩⟩
  have hbG : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨n, hn', hnb⟩ := htrans (f z) ⟨z, rfl⟩ hz b b.property hbG
  let d : G := (f z)⁻¹ * b
  have hdQ : d ∈ f.range := f.range.mul_mem (f.range.inv_mem ⟨z, rfl⟩) b.property
  have hd1 : d ≠ 1 := by
    intro he
    exact hbz (Subtype.ext (inv_mul_eq_one.mp he).symm)
  have hdU : d ∈ U := by
    have hconj := projection_conjugate f hc z hn'.1
    rw [hnb] at hconj
    have hh := U.mul_mem (U.inv_mem z.property)
      ((mem_normalizer_iff.mp (hn hn') (z : G)).mp z.property)
    rw [hconj] at hh
    simpa only [mul_assoc, inv_mul_cancel_left] using hh
  intro q hq
  by_cases hq1 : q = 1
  · exact hq1 ▸ U.one_mem
  obtain ⟨m, hm, hmq⟩ := htrans d hdQ hd1 q hq hq1
  exact hmq ▸ ((mem_normalizer_iff.mp (hn hm) d).mp hdU)

/-- Once the projection lies in U, its central residual lies in U as well,
giving the actual centralizer/intersection decomposition. -/
theorem projection_split_of_range_le (f : U →* G) (hf : f.range ≤ L)
    (hc : ∀ u : U, (u : G) * (f u)⁻¹ ∈ centralizer (L : Set G))
    (hU : f.range ≤ U) :
    U = (U ⊓ centralizer (L : Set G)) ⊔ (U ⊓ L) := by
  apply le_antisymm
  · intro u hu
    have hp : f ⟨u, hu⟩ ∈ f.range := ⟨⟨u, hu⟩, rfl⟩
    have hmem := ((U ⊓ centralizer (L : Set G)) ⊔ (U ⊓ L)).mul_mem
      ((le_sup_left : U ⊓ centralizer (L : Set G) ≤ _ ⊔ (U ⊓ L)) (show u * (f ⟨u, hu⟩)⁻¹ ∈ U ⊓ centralizer (L : Set G) from
        ⟨U.mul_mem hu (U.inv_mem (hU hp)), hc ⟨u, hu⟩⟩))
      ((le_sup_right : U ⊓ L ≤ (U ⊓ centralizer (L : Set G)) ⊔ _) (show f ⟨u, hu⟩ ∈ U ⊓ L from ⟨hU hp, hf hp⟩))
    simpa only [inv_mul_cancel_right] using hmem
  · exact sup_le inf_le_left inf_le_left

/-- For a centerless factor the projected subgroup is the literal U∩L. -/
theorem projection_range_eq_inf_of_disjoint (f : U →* G) (hf : f.range ≤ L)
    (hc : ∀ u : U, (u : G) * (f u)⁻¹ ∈ centralizer (L : Set G))
    (hU : f.range ≤ U) (hdis : Disjoint L (centralizer (L : Set G))) :
    f.range = U ⊓ L := by
  apply le_antisymm (le_inf hU hf)
  intro u hu
  have hp : f ⟨u, hu.1⟩ ∈ f.range := ⟨⟨u, hu.1⟩, rfl⟩
  have he : u * (f ⟨u, hu.1⟩)⁻¹ = 1 := by
    exact hdis.le_bot ⟨L.mul_mem hu.2 (L.inv_mem (hf hp)), hc ⟨u, hu.1⟩⟩
  exact (mul_inv_eq_one.mp he).symm ▸ hp

end Subgroup.CentralFactor
