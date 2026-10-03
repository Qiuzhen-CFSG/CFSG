module
public import ABG.ChapterII.Section1.Center
public import Theory.GroupTheory.DihedralPresentation

/-!
# The central quotient of a quasi-dihedral group

The quotient of a quasi-dihedral group by its center is dihedral. More
precisely, a group of order `2^n` with the semidihedral presentation, `n ≥ 4`,
has central quotient isomorphic to `DihedralGroup (2^(n-2))`. This module
completes Chapter II, §1, Lemma 1(v), article p. 9, of
`refs/latex/alperin-brauer-gorenstein.tex`; `Center` proves that the center
has order two.

Map the presentation generators to the quotient. The half-order power of
the cyclic generator lies in the center, so it becomes trivial, and the
conjugation relation becomes inversion. The generator images still generate
by the image-of-closure theorem. The quotient cardinality is half the group
cardinality. The shared dihedral recognition theorem identifies a group with
these relations, generation, and cardinality with the concrete dihedral model.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]

private theorem quotient_relations {n : ℕ} (hn : 4 ≤ n) (a b : G)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    let q := QuotientGroup.mk' (Subgroup.center G)
    (q a) ^ (2 ^ (n - 2)) = 1 ∧ (q b) ^ 2 = 1 ∧
      q b * q a * (q b)⁻¹ = (q a)⁻¹ ∧
      Subgroup.closure ({q a, q b} : Set (G ⧸ Subgroup.center G)) = ⊤ := by
  dsimp only
  let q := QuotientGroup.mk' (Subgroup.center G)
  have hapow : (q a) ^ (2 ^ (n - 2)) = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (half_order_pow_mem_center hn a b ha hb hconj hgen)
  refine ⟨hapow, ?_, ?_, ?_⟩
  · change (q b) ^ 2 = 1
    rw [← map_pow, ← hb, pow_orderOf_eq_one, map_one]
  · change q b * q a * (q b)⁻¹ = (q a)⁻¹
    have h : q b * q a * (q b)⁻¹ = (q a) ^ (2 ^ (n - 2) - 1) := by
      simpa only [map_mul, map_inv, map_pow] using congrArg q hconj
    rw [h]
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide) : 1 ≤ 2 ^ (n - 2))]
    exact hapow
  · have h := congrArg (fun H : Subgroup G => H.map q) hgen
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    simpa only [Set.image_insert_eq, Set.image_singleton] using h

private theorem quotient_card {n : ℕ} (hcard : Nat.card G = 2 ^ n)
    (hcenter : Nat.card (Subgroup.center G) = 2) (hn : 2 ≤ n) :
    Nat.card (G ⧸ Subgroup.center G) = 2 * 2 ^ (n - 2) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
  rw [hcard, hcenter] at h
  have he : n = (n - 2) + 1 + 1 := by omega
  rw [he, pow_succ, pow_succ] at h
  omega

/-- The central quotient has the precise dihedral parameter determined by the presentation. -/
public theorem central_quotient_equiv {n : ℕ} (hn : 4 ≤ n)
    (hcard : Nat.card G = 2 ^ n) (a b : G)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    Nonempty ((G ⧸ Subgroup.center G) ≃* DihedralGroup (2 ^ (n - 2))) := by
  have hG : Stellmacher.IsSemidihedralGroup G :=
    ⟨n, hn, hcard, a, b, ha, hb, hconj, hgen⟩
  obtain ⟨hc, hd, hi, hg⟩ := quotient_relations hn a b ha hb hconj hgen
  exact dihedralGroup_equiv_of_relations (by positivity) _ _ hc hd hi hg
    (quotient_card hcard (card_center hG) (by omega))

/-- The quotient of a quasi-dihedral group by its center is dihedral (ABG II.1.1(v)). -/
public theorem central_quotient_isDihedral
    (hG : Stellmacher.IsSemidihedralGroup G) :
    Stellmacher.IsDihedralGroup (G ⧸ Subgroup.center G) := by
  obtain ⟨n, hn, hcard, a, b, ha, hb, hconj, hgen⟩ := hG
  exact ⟨2 ^ (n - 2), central_quotient_equiv hn hcard a b ha hb hconj hgen⟩
end ABG.QuasiDihedral
