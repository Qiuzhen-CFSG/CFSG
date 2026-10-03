module
public import Theory.GroupTheory.PGroup.TrivialImage

/-!
# Characteristic kernels of p-group quotients

A subgroup with no normal subgroup of index p has trivial image in every
finite p-group. Restricting quotient maps therefore places it in every normal
subgroup with p-group quotient. If its own quotient is a p-group, composing
the quotient map with automorphisms proves characteristicity, and mutual
containment proves uniqueness. A p-group supplement supplies the quotient
hypothesis by surjecting onto the quotient.

These are the universal-property arguments for the p-residual, stated without
introducing another residual definition. They generalize the characteristic
SL2 lift argument in Alperin--Brauer--Gorenstein, II.3 Proposition 2,
article pages 22--23, and do not require perfectness.
-/

namespace Subgroup

/-- A p-group supplement makes the quotient by a normal subgroup a p-group. -/
public theorem quotient_isPGroup_of_sup_eq_top
    {G : Type*} [Group G] {p : ℕ}
    (Z L : Subgroup G) [L.Normal] (hZ : IsPGroup p Z) (hsup : Z ⊔ L = ⊤) :
    IsPGroup p (G ⧸ L) := by
  let q := QuotientGroup.mk' L
  apply hZ.of_surjective (q.domRestrict Z)
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective L x
  have hg : g ∈ Z ⊔ L := by rw [hsup]; trivial
  obtain ⟨z, hz, l, hl, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  refine ⟨⟨z, hz⟩, ?_⟩
  change q z = q (z * l)
  have hlq : q l = 1 := (QuotientGroup.eq_one_iff (N := L) (x := l)).mpr hl
  rw [map_mul, hlq, mul_one]

/-- This is the universal containment property of the p-residual. -/
public theorem le_normal_of_no_normal_index_prime
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (L N : Subgroup G) [N.Normal]
    (hL : ∀ K : Subgroup L, K.Normal → K.index ≠ p)
    (hN : IsPGroup p (G ⧸ N)) : L ≤ N := by
  intro l hl
  have h := MonoidHom.eq_one_of_no_normal_index_prime hL hN
    ((QuotientGroup.mk' N).comp L.subtype) ⟨l, hl⟩
  exact (QuotientGroup.eq_one_iff (N := N) (x := l)).mp h

/-- A normal subgroup with p-group quotient and no normal subgroup of index
p is characteristic. -/
public theorem characteristic_of_no_normal_index_prime
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (L : Subgroup G) [L.Normal]
    (hL : ∀ K : Subgroup L, K.Normal → K.index ≠ p)
    (hquot : IsPGroup p (G ⧸ L)) : L.Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro e l hl
  have h := MonoidHom.eq_one_of_no_normal_index_prime hL hquot
    ((QuotientGroup.mk' L).comp (e.toMonoidHom.comp L.subtype)) ⟨l, hl⟩
  exact (QuotientGroup.eq_one_iff (N := L) (x := e l)).mp h

/-- Two normal subgroups with p-group quotients and no normal subgroups of
index p are equal. -/
public theorem eq_of_no_normal_index_prime
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (L M : Subgroup G) [L.Normal] [M.Normal]
    (hL : ∀ K : Subgroup L, K.Normal → K.index ≠ p)
    (hM : ∀ K : Subgroup M, K.Normal → K.index ≠ p)
    (hquotL : IsPGroup p (G ⧸ L)) (hquotM : IsPGroup p (G ⧸ M)) : L = M := by
  exact le_antisymm (le_normal_of_no_normal_index_prime L M hL hquotM)
    (le_normal_of_no_normal_index_prime M L hM hquotL)

end Subgroup
