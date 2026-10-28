module

public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy.Reduction

/-!
# The subgroup calculation in the root semilinear overgroup

An invariant subgroup containing the diagonal torus and bounded by the
inner--semilinear join is exactly the inner--actor join. Diagonal scalings,
graph and field give four literal normal forms. Their intersection with the
inner automorphisms is trivial. A central nonidentity outer coset must have a
diagonal representative, which excludes pure Frobenius. Full action on the
root center then produces graph--field; adjoining graph would produce the
excluded Frobenius. This also proves both inclusions in the subgroup equality.

Torus alignment and the semilinear bound remain explicit inputs supplied by
the parent recognition argument. Source motivation: Aschbacher, *Sporadic
Groups* (1994), 8.15(5--6), 46.3(2), and 46.14, pp.29--30, 251, 257--258.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy
open Matrix.PSL3Four.RootNormalizerModel
noncomputable section

private abbrev frob : MulAut Root := SylowModel.frob
private abbrev gr : MulAut Root := graph

private def sigma : Fˣ →* Fˣ := Units.map fieldFrobenius.toMonoidHom

private theorem graph_sq : gr * gr = 1 := by
  apply MulEquiv.ext
  intro q
  refine SylowModel.U.ext rfl rfl ?_
  change q.y * q.x - (q.x * q.y - q.c) = q.c
  ring

private theorem graph_diagonal (a : Fˣ × Fˣ) :
    gr * diagonalHom a = diagonalHom (a.2, a.1) * gr := by
  apply MulEquiv.ext
  intro q
  apply SylowModel.U.ext <;> simp [gr, graph, diagonalHom, diagonal]
  ring

private theorem frob_sq : frob * frob = 1 := by simpa only [pow_two] using SylowModel.frob_sq

private theorem graph_frob_commute : gr * frob = frob * gr := by
  apply MulEquiv.ext
  intro q
  refine SylowModel.U.ext rfl rfl ?_
  change fieldFrobenius q.x * fieldFrobenius q.y - fieldFrobenius q.c =
    fieldFrobenius (q.x * q.y - q.c)
  rw [map_sub, map_mul]

private theorem frob_diagonal (a : Fˣ × Fˣ) :
    frob * diagonalHom a = diagonalHom (sigma a.1, sigma a.2) * frob := by
  apply MulEquiv.ext
  intro q
  apply SylowModel.U.ext <;>
    simp [frob, SylowModel.frob, diagonalHom, diagonal, sigma, mul_pow]

private theorem diagonal_mem_inner_iff (a : Fˣ × Fˣ) :
    diagonalHom a ∈ inner ↔ a = 1 := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := h
    have hx := congrArg (fun t : MulAut Root => (t ⟨1, 0, 0⟩).x) hq
    have hy := congrArg (fun t : MulAut Root => (t ⟨0, 1, 0⟩).y) hq
    apply Prod.ext
    · apply Units.ext
      change (a.1 : F) = 1
      change q.x + 1 + -q.x = (a.1 : F) * 1 at hx
      simpa only [mul_one, add_right_comm, add_neg_cancel, zero_add] using hx.symm
    · apply Units.ext
      change (a.2 : F) = 1
      change q.y + 1 + -q.y = (a.2 : F) * 1 at hy
      simpa only [mul_one, add_right_comm, add_neg_cancel, zero_add] using hy.symm
  · rintro rfl
    simpa only [map_one] using inner.one_mem

private theorem normalizes_of_conj_le {G : Type*} [Group G] (K : Subgroup G)
    (w : G) (hw : w * w = 1)
    (h : K.map (MulAut.conj w).toMonoidHom ≤ K) : w ∈ normalizer (K : Set G) := by
  have hi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hh (x : G) (hx : x ∈ K) : w * x * w ∈ K := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hi] using
      h (mem_map_of_mem _ hx)
  rw [mem_normalizer_iff]
  intro x
  rw [hi]
  exact ⟨hh x, fun hx => by
    have he : w * (w * x * w) * w = x := by
      calc
        _ = (w * w) * x * (w * w) := by simp only [mul_assoc]
        _ = x := by rw [hw, one_mul, mul_one]
    simpa only [he] using hh _ hx⟩

private theorem involution_join_form {G : Type*} [Group G] (K : Subgroup G)
    (w : G) (hw : w * w = 1) (hn : w ∈ normalizer (K : Set G))
    {x : G} (hx : x ∈ K ⊔ zpowers w) : ∃ k ∈ K, x = k ∨ x = k * w := by
  open scoped Pointwise in
    have hx' : x ∈ (K : Set G) * (zpowers w : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left K (zpowers w) (zpowers_le.mpr hn)]
      exact hx
    obtain ⟨k, hk, t, ht, rfl⟩ := hx'
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ht
    have hn' := zpow_eq_zpow_emod n (show w ^ (2 : ℤ) = 1 by simpa [pow_two] using hw)
    have hn2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
    refine ⟨k, hk, ?_⟩
    rcases hn2 with h | h <;> simp [hn', h]

private theorem graph_normalizes : gr ∈ normalizer (torus : Set (MulAut Root)) := by
  apply normalizes_of_conj_le _ _ graph_sq
  rintro x ⟨y, ⟨a, rfl⟩, rfl⟩
  refine ⟨(a.2, a.1), ?_⟩
  change diagonalHom (a.2, a.1) = gr * diagonalHom a * gr⁻¹
  rw [inv_eq_of_mul_eq_one_right graph_sq, graph_diagonal, mul_assoc, graph_sq, mul_one]

private theorem frob_normalizes : frob ∈ normalizer (torus : Set (MulAut Root)) := by
  apply normalizes_of_conj_le _ _ frob_sq
  rintro x ⟨y, ⟨a, rfl⟩, rfl⟩
  refine ⟨(sigma a.1, sigma a.2), ?_⟩
  change diagonalHom (sigma a.1, sigma a.2) = frob * diagonalHom a * frob⁻¹
  rw [inv_eq_of_mul_eq_one_right frob_sq, frob_diagonal, mul_assoc, frob_sq, mul_one]

private theorem frob_normalizes_graphJoin :
    frob ∈ normalizer ((torus ⊔ zpowers gr : Subgroup (MulAut Root)) : Set (MulAut Root)) := by
  apply normalizes_of_conj_le _ _ frob_sq
  rw [Subgroup.map_sup]
  apply sup_le
  · rintro x ⟨y, hy, rfl⟩
    exact mem_sup_left ((mem_normalizer_iff.mp frob_normalizes y).mp hy)
  · rw [MonoidHom.map_zpowers]
    apply zpowers_le.mpr
    have he : (MulAut.conj frob) gr = gr := by
      change frob * gr * frob⁻¹ = gr
      rw [← graph_frob_commute, mul_assoc, mul_inv_cancel, mul_one]
    simpa only [MulEquiv.coe_toMonoidHom, he] using
      (mem_sup_right (mem_zpowers gr) : gr ∈ torus ⊔ zpowers gr)

/-- The four literal diagonal, graph, field and graph--field normal forms. -/
theorem semilinear_normal_form {x : MulAut Root} (hx : x ∈ semilinear) :
    ∃ a : Fˣ × Fˣ, x = diagonalHom a ∨ x = diagonalHom a * graph ∨
      x = diagonalHom a * SylowModel.frob ∨ x = diagonalHom a * graphField := by
  obtain ⟨k, hk, rfl | rfl⟩ := involution_join_form _ _ frob_sq frob_normalizes_graphJoin hx
  · obtain ⟨d, ⟨a, rfl⟩, rfl | rfl⟩ := involution_join_form _ _ graph_sq graph_normalizes hk
    · exact ⟨a, Or.inl rfl⟩
    · exact ⟨a, Or.inr (Or.inl rfl)⟩
  · obtain ⟨d, ⟨a, rfl⟩, rfl | rfl⟩ := involution_join_form _ _ graph_sq graph_normalizes hk
    · exact ⟨a, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨a, Or.inr (Or.inr (Or.inr (by rw [mul_assoc, graph_frob_commute]; rfl)))⟩

private theorem inner_xy {s : MulAut Root} (hs : s ∈ inner) (q : Root) :
    (s q).x = q.x ∧ (s q).y = q.y := by
  obtain ⟨r, rfl⟩ := hs
  change r.x + q.x + -r.x = q.x ∧ r.y + q.y + -r.y = q.y
  constructor <;> rw [add_right_comm, add_neg_cancel, zero_add]

private theorem inner_fixes_center {s : MulAut Root} (hs : s ∈ inner) (c : F) :
    s ⟨0, 0, c⟩ = ⟨0, 0, c⟩ := by
  obtain ⟨r, rfl⟩ := hs
  apply SylowModel.U.ext
  · change r.x + 0 + -r.x = 0
    simp only [add_zero, add_neg_cancel]
  · change r.y + 0 + -r.y = 0
    simp only [add_zero, add_neg_cancel]
  · change (r.c + c + r.x * 0) + (r.x * r.y - r.c) + (r.x + 0) * -r.y = c
    ring

/-- The semilinear coordinate maps have no nonidentity inner automorphism. -/
theorem inner_disjoint_semilinear : Disjoint inner semilinear := by
  rw [disjoint_def]
  intro s hs ht
  obtain ⟨a, rfl | rfl | rfl | rfl⟩ := semilinear_normal_form ht
  · rw [(diagonal_mem_inner_iff a).mp hs, map_one]
  · have he := (inner_xy hs ⟨1, 0, 0⟩).1
    simp [diagonalHom, diagonal, graph] at he
  · have ha : (a.1 : F) = 1 := by
      simpa [diagonalHom, diagonal, SylowModel.frob] using (inner_xy hs ⟨1, 0, 0⟩).1
    obtain ⟨c, hc⟩ := exists_fieldFrobenius_ne
    exact (hc (by simpa [diagonalHom, diagonal, SylowModel.frob, ha] using
      (inner_xy hs ⟨c, 0, 0⟩).1)).elim
  · have he := (inner_xy hs ⟨1, 0, 0⟩).1
    simp [diagonalHom, diagonal, graphField, graph, SylowModel.frob] at he

private theorem diagonal_mem (a : Fˣ × Fˣ) : diagonalHom a ∈ semilinear :=
  mem_sup_left (mem_sup_left ⟨a, rfl⟩)

private theorem frob_mem : frob ∈ semilinear := mem_sup_right (mem_zpowers _)

private theorem exists_unit_moved : ∃ u : Fˣ, fieldFrobenius (u : F) ≠ u := by
  obtain ⟨c, hc⟩ := exists_fieldFrobenius_ne
  have hc0 : c ≠ 0 := by intro h; subst c; simp at hc
  exact ⟨Units.mk0 c hc0, hc⟩

private theorem semilinear_centralizes_torus {s : MulAut Root} (hs : s ∈ semilinear)
    (hc : ∀ a : Fˣ × Fˣ, Commute s (diagonalHom a)) : s ∈ torus := by
  obtain ⟨u, hu⟩ := exists_unit_moved
  have hu1 : (u : F) ≠ 1 := by intro h; rw [h, map_one] at hu; exact hu rfl
  obtain ⟨a, rfl | rfl | rfl | rfl⟩ := semilinear_normal_form hs
  · exact ⟨a, rfl⟩
  · have he := congrArg (fun t : MulAut Root => (t ⟨1, 0, 0⟩).y) (hc (u, 1)).eq
    have he' : (a.2 : F) * u = (a.2 : F) := by
      simpa [diagonalHom, diagonal, graph] using he
    exact (hu1 ((mul_eq_left₀ a.2.ne_zero).mp he')).elim
  · have he := congrArg (fun t : MulAut Root => (t ⟨1, 0, 0⟩).x) (hc (u, 1)).eq
    have he' : (a.1 : F) * fieldFrobenius (u : F) = (a.1 : F) * u := by
      simpa [diagonalHom, diagonal, SylowModel.frob, mul_comm] using he
    exact (hu (mul_left_cancel₀ a.1.ne_zero he')).elim
  · have he := congrArg (fun t : MulAut Root => (t ⟨1, 0, 0⟩).y) (hc (u, 1)).eq
    have he' : (a.2 : F) * fieldFrobenius (u : F) = (a.2 : F) := by
      simpa [diagonalHom, diagonal, graphField, graph, SylowModel.frob] using he
    have hf : fieldFrobenius (u : F) = 1 := (mul_eq_left₀ a.2.ne_zero).mp he'
    exact (hu1 (fieldFrobenius.injective (hf.trans (map_one _).symm))).elim

private theorem commute_of_inner_factor {u s t : MulAut Root}
    (hu : u ∈ inner) (hs : s ∈ semilinear) (ht : t ∈ semilinear)
    (hc : ⁅u * s, t⁆ ∈ inner) : Commute s t := by
  let π := QuotientGroup.mk' inner
  have hpu : π u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
  have hpc : π ⁅u * s, t⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hc
  have hpst : π ⁅s, t⁆ = 1 := by
    simpa only [map_commutatorElement, map_mul, hpu, one_mul] using hpc
  have hist : ⁅s, t⁆ ∈ inner := (QuotientGroup.eq_one_iff _).mp hpst
  have hslt : ⁅s, t⁆ ∈ semilinear := by
    rw [commutatorElement_def]
    exact semilinear.mul_mem (semilinear.mul_mem (semilinear.mul_mem hs ht)
      (semilinear.inv_mem hs)) (semilinear.inv_mem ht)
  exact commutatorElement_eq_one_iff_commute.mp
    (disjoint_def.mp inner_disjoint_semilinear hist hslt)

private theorem unit_fixed_eq_one (u : Fˣ) (h : sigma u = u) : u = 1 := by
  apply Units.ext
  have h' : (u : F) * u = (u : F) := by
    have he := congrArg Units.val h
    change (u : F) ^ 2 = (u : F) at he
    simpa only [pow_two] using he
  exact (mul_eq_left₀ u.ne_zero).mp h'

private theorem field_not_mem {H : Subgroup (MulAut Root)} (h : AutomizerInvariants H)
    (hT : torus ≤ H) (hbound : H ≤ inner ⊔ semilinear) : frob ∉ H := by
  intro hf
  obtain ⟨c, hc, hcnot, -, hcomm⟩ := h.central_cubic
  obtain ⟨u, hu, s, hs, rfl⟩ := mem_sup_of_normal_left.mp (hbound hc)
  have hsT : s ∈ torus := semilinear_centralizes_torus hs (fun a =>
    commute_of_inner_factor hu hs (diagonal_mem a) (hcomm _ (hT ⟨a, rfl⟩)))
  obtain ⟨a, rfl⟩ := hsT
  have he := (commute_of_inner_factor hu hs frob_mem (hcomm _ hf)).eq
  rw [frob_diagonal] at he
  have hae := Cubic.diagonalHom_injective (mul_right_cancel he)
  have ha : a = 1 := Prod.ext
    (unit_fixed_eq_one a.1 (congrArg Prod.fst hae).symm)
    (unit_fixed_eq_one a.2 (congrArg Prod.snd hae).symm)
  apply hcnot
  simpa only [ha, map_one, mul_one] using hu

private theorem remove_factors {H : Subgroup (MulAut Root)} (hI : inner ≤ H)
    (hT : torus ≤ H) {u t : MulAut Root} (hu : u ∈ inner) (a : Fˣ × Fˣ)
    (ht : u * (diagonalHom a * t) ∈ H) : t ∈ H := by
  exact (H.mul_mem_cancel_left (hT ⟨a, rfl⟩)).mp
    ((H.mul_mem_cancel_left (hI hu)).mp ht)

private theorem graphField_mem_of_invariants {H : Subgroup (MulAut Root)}
    (h : AutomizerInvariants H) (hT : torus ≤ H) (hbound : H ≤ inner ⊔ semilinear) :
    graphField ∈ H := by
  obtain ⟨s, hs, hcenter⟩ := h.full_center_action (centerCongr SylowModel.frob)
  obtain ⟨u, hu, t, ht, rfl⟩ := mem_sup_of_normal_left.mp (hbound hs)
  have hc (c : F) : (u * t) ⟨0, 0, c⟩ = SylowModel.frob ⟨0, 0, c⟩ :=
    hcenter ⟨⟨0, 0, c⟩, (SylowModel.mem_center_U _).mpr ⟨rfl, rfl⟩⟩
  obtain ⟨a, rfl | rfl | rfl | rfl⟩ := semilinear_normal_form ht
  · have he (c : F) : ((a.1 : F) * a.2) * c = fieldFrobenius c := by
      have hh := hc c
      change u ⟨(a.1 : F) * 0, (a.2 : F) * 0, ((a.1 : F) * a.2) * c⟩ = _ at hh
      simp only [mul_zero] at hh
      rw [inner_fixes_center hu] at hh
      exact congrArg SylowModel.U.c hh
    have hab : (a.1 : F) * a.2 = 1 := by simpa using he 1
    obtain ⟨c, hc⟩ := exists_fieldFrobenius_ne
    exact (hc (by simpa only [hab, one_mul] using (he c).symm)).elim
  · have he (c : F) : ((a.1 : F) * a.2) * -c = fieldFrobenius c := by
      have hh := hc c
      change u ⟨(a.1 : F) * 0, (a.2 : F) * 0,
        ((a.1 : F) * a.2) * (0 * 0 - c)⟩ = _ at hh
      simp only [mul_zero, zero_sub] at hh
      rw [inner_fixes_center hu] at hh
      exact congrArg SylowModel.U.c hh
    have hab : (a.1 : F) * a.2 = 1 := by simpa [CharTwo.neg_eq] using he 1
    obtain ⟨c, hc⟩ := exists_fieldFrobenius_ne
    exact (hc (by simpa only [hab, one_mul, CharTwo.neg_eq] using (he c).symm)).elim
  · exact (field_not_mem h hT hbound (remove_factors h.inner_le hT hu a hs)).elim
  · exact remove_factors h.inner_le hT hu a hs

/-- The invariant subgroup is the literal inner--actor join.  Torus alignment
and the semilinear upper bound are the only external coordinate premises. -/
theorem eq_standard_of_semilinear (H : Subgroup (MulAut Root))
    (h : AutomizerInvariants H) (hT : torus ≤ H) (hbound : H ≤ inner ⊔ semilinear) :
    H = inner ⊔ RootNormalizerModel.actor := by
  have hgf := graphField_mem_of_invariants h hT hbound
  have hf := field_not_mem h hT hbound
  have hg : graph ∉ H := by
    intro hg
    apply hf
    have hh := H.mul_mem hgf hg
    have he : graphField * graph = frob := by
      change (frob * gr) * gr = frob
      rw [mul_assoc, graph_sq, mul_one]
    exact he ▸ hh
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, t, ht, rfl⟩ := mem_sup_of_normal_left.mp (hbound hx)
    obtain ⟨a, rfl | rfl | rfl | rfl⟩ := semilinear_normal_form ht
    · exact mul_mem_sup hu (mem_sup_left ⟨a, rfl⟩)
    · exact (hg (remove_factors h.inner_le hT hu a hx)).elim
    · exact (hf (remove_factors h.inner_le hT hu a hx)).elim
    · exact mul_mem_sup hu (actor.mul_mem (mem_sup_left ⟨a, rfl⟩)
        (mem_sup_right (mem_zpowers graphField)))
  · exact sup_le h.inner_le (sup_le hT (zpowers_le.mpr hgf))

end
end Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy
