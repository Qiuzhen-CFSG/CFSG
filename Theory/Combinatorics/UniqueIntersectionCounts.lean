module
public import Theory.Combinatorics.RegularConfiguration
public import Theory.Combinatorics.RegularConfigurationConfig

/-!
# A plane from uniform pencils and unique intersections

Suppose there are `q² + q + 1` lines, each point lies on `q + 1` lines,
and each two distinct lines have exactly one common point. Counting the
other lines through points on a fixed line gives `q + 1` points on that
line. Counting all incidences then gives `q² + q + 1` points. For `q > 1`,
the regular configuration lemmas construct the projective plane on the
original incidence relation.

This is the final counting argument in Wong, *On finite groups whose
2-Sylow subgroups have cyclic subgroups of index 2* (1964), Theorem 6(b),
p.111. No group-theoretic or projective-plane hypothesis is used here.
-/

namespace Configuration

variable {P L : Type*} [Membership P L] [Finite P] [Finite L]

/-- An upper bound on the number of points can replace the uniqueness
argument: all ordered pairs of distinct lines already exhaust the available
incidences. This is useful when points are fibers of a group-theoretic map. -/
public theorem unique_intersections_of_point_bound (q : ℕ)
    (hL : Nat.card L = q ^ 2 + q + 1)
    (hP : Nat.card P ≤ q ^ 2 + q + 1)
    (hlines : ∀ p : P, lineCount L p = q + 1)
    (hinter : ∀ l m : L, l ≠ m → ∃ p : P, p ∈ l ∧ p ∈ m) :
    ∀ l m : L, l ≠ m → ∃! p : P, p ∈ l ∧ p ∈ m := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let : Fintype L := Fintype.ofFinite L
  let T := Σ p : P, Σ l : {l : L // p ∈ l}, {m : {m : L // p ∈ m} // m ≠ l}
  let U := Σ l : L, {m : L // m ≠ l}
  let f : T → U := fun x => ⟨x.2.1.1, ⟨x.2.2.1.1, fun h => x.2.2.2 (Subtype.ext h)⟩⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨l, m, hm⟩
    obtain ⟨p, hpl, hpm⟩ := hinter l m hm.symm
    exact ⟨⟨p, ⟨l, hpl⟩, ⟨⟨m, hpm⟩, fun h => hm (congrArg Subtype.val h)⟩⟩, rfl⟩
  have hT : Nat.card T = Nat.card P * ((q + 1) * q) := by
    dsimp only [T]
    simp only [Nat.card_sigma]
    have hrest (p : P) (l : {l : L // p ∈ l}) :
        Nat.card {m : {m : L // p ∈ m} // m ≠ l} = q := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun m => m = l),
        Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card]
      change lineCount L p - 1 = q
      rw [hlines, Nat.add_sub_cancel]
    simp_rw [hrest]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card]
    change (∑ p : P, lineCount L p * q) = _
    simp_rw [hlines]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  have hU : Nat.card U = (q ^ 2 + q + 1) * ((q + 1) * q) := by
    dsimp only [U]
    rw [Nat.card_sigma]
    have hrest (l : L) : Nat.card {m : L // m ≠ l} = (q + 1) * q := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun m => m = l),
        Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hL, Nat.add_sub_cancel]
      ring
    simp_rw [hrest]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, hL]
  have hle : Nat.card T ≤ Nat.card U := by
    rw [hT, hU]
    exact Nat.mul_le_mul_right _ hP
  have heq : Nat.card T = Nat.card U :=
    le_antisymm hle (Nat.card_le_card_of_surjective f hsurj)
  have hinj := ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hsurj, heq⟩).1
  intro l m hlm
  obtain ⟨p, hp⟩ := hinter l m hlm
  refine ⟨p, hp, ?_⟩
  intro r hr
  let tp : T := ⟨p, ⟨l, hp.1⟩, ⟨⟨m, hp.2⟩, fun h => hlm (congrArg Subtype.val h).symm⟩⟩
  let tr : T := ⟨r, ⟨l, hr.1⟩, ⟨⟨m, hr.2⟩, fun h => hlm (congrArg Subtype.val h).symm⟩⟩
  exact congrArg (fun t : T => t.1) (hinj (show f tr = f tp from rfl))

/-- Count other lines by their unique intersection with a fixed line. -/
public theorem pointCount_of_unique_intersections (q : ℕ) (hq : 0 < q)
    (hL : Nat.card L = q ^ 2 + q + 1)
    (hlines : ∀ p : P, lineCount L p = q + 1)
    (hinter : ∀ l m : L, l ≠ m → ∃! p : P, p ∈ l ∧ p ∈ m)
    (l : L) : pointCount P l = q + 1 := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let : Fintype L := Fintype.ofFinite L
  let T := Σ p : {p : P // p ∈ l}, {m : L // p.1 ∈ m ∧ m ≠ l}
  let f : T → {m : L // m ≠ l} := fun t => ⟨t.2.1, t.2.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hm : a.2.1 = b.2.1 := congrArg Subtype.val hab
      have hp : a.1 = b.1 := by
        apply Subtype.ext
        obtain ⟨p, _, hu⟩ := hinter l a.2.1 a.2.2.2.symm
        exact (hu a.1 ⟨a.1.2, a.2.2.1⟩).trans
          (hu b.1 ⟨b.1.2, hm ▸ b.2.2.1⟩).symm
      cases a
      cases b
      dsimp at hp hm
      subst hp
      congr
      exact Subtype.ext hm
    · rintro ⟨m, hm⟩
      obtain ⟨p, hp, _⟩ := hinter l m hm.symm
      exact ⟨⟨⟨p, hp.1⟩, ⟨m, hp.2, hm⟩⟩, rfl⟩
  have hT : Nat.card T = pointCount P l * q := by
    dsimp only [T]
    rw [Nat.card_sigma]
    have hcount (p : {p : P // p ∈ l}) :
        Nat.card {m : L // p.1 ∈ m ∧ m ≠ l} = q := by
      rw [← Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun m : L => p.1 ∈ m) (fun m => m ≠ l))]
      simp only [Nat.card_eq_fintype_card]
      rw [Fintype.card_subtype_compl (fun m : {m : L // p.1 ∈ m} => m.1 = l)]
      have hone : Fintype.card {m : {m : L // p.1 ∈ m} // m.1 = l} = 1 := by
        simpa only [Subtype.ext_iff] using
          Fintype.card_subtype_eq (⟨l, p.2⟩ : {m : L // p.1 ∈ m})
      rw [hone, ← Nat.card_eq_fintype_card]
      change lineCount L p.1 - 1 = q
      rw [hlines, Nat.add_sub_cancel]
    simp_rw [hcount]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card, pointCount]
  have hrest : Nat.card {m : L // m ≠ l} = (q + 1) * q := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun m : L => m = l),
      Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hL, Nat.add_sub_cancel]
    ring
  have heq := Nat.card_congr (Equiv.ofBijective f hf)
  rw [hT, hrest] at heq
  exact Nat.eq_of_mul_eq_mul_right hq heq

/-- Count all incident point-line pairs in the two possible orders. -/
public theorem card_points_of_unique_intersections (q : ℕ) (hq : 0 < q)
    (hL : Nat.card L = q ^ 2 + q + 1)
    (hlines : ∀ p : P, lineCount L p = q + 1)
    (hinter : ∀ l m : L, l ≠ m → ∃! p : P, p ∈ l ∧ p ∈ m) :
    Nat.card P = q ^ 2 + q + 1 := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let : Fintype L := Fintype.ofFinite L
  let e : (Σ p : P, {l : L // p ∈ l}) ≃ (Σ l : L, {p : P // p ∈ l}) :=
    { toFun := fun x => ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
      invFun := fun x => ⟨x.2.1, ⟨x.1, x.2.2⟩⟩ }
  have heq := Nat.card_congr e
  simp only [Nat.card_sigma] at heq
  change (∑ p : P, lineCount L p) = ∑ l : L, pointCount P l at heq
  simp_rw [hlines, pointCount_of_unique_intersections q hq hL hlines hinter] at heq
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card] at heq
  exact (Nat.eq_of_mul_eq_mul_right (by omega : 0 < q + 1) heq).trans hL

/-- Uniform pencils and unique line intersections at projective size supply
the projective-plane structure on the given incidence relation. -/
@[instance_reducible] public noncomputable def projectivePlane_of_unique_intersections
    (q : ℕ) (hq : 1 < q) (hL : Nat.card L = q ^ 2 + q + 1)
    (hlines : ∀ p : P, lineCount L p = q + 1)
    (hinter : ∀ l m : L, l ≠ m → ∃! p : P, p ∈ l ∧ p ∈ m) :
    ProjectivePlane P L := by
  let : Fintype P := Fintype.ofFinite P
  let : Fintype L := Fintype.ofFinite L
  have hP := card_points_of_unique_intersections q (by omega) hL hlines hinter
  have hpoints := pointCount_of_unique_intersections q (by omega) hL hlines hinter
  have hex (l m : L) (h : l ≠ m) := (hinter l m h).exists
  letI : Nondegenerate P L :=
    nondegenerate_of_regular_counts q hq hP hL hpoints hlines hex
  letI : HasPoints P L :=
    { ‹Nondegenerate P L› with
      mkPoint := fun {l m} h => (hex l m h).choose
      mkPoint_ax := fun {l m} h => (hex l m h).choose_spec }
  letI : HasLines P L := HasPoints.hasLines
    (by simpa only [Nat.card_eq_fintype_card] using hP.trans hL.symm)
  exact { ‹HasPoints P L›, ‹HasLines P L› with
    exists_config := exists_config_of_regular_counts q hq hP hpoints hlines }

end Configuration
