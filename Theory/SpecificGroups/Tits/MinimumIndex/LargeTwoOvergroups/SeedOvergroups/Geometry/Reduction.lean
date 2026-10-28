module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.FiniteCover

/-!
# Geometry from common factors and representative supports

If every listed factor lies in every place, left multiplication by a factor
preserves all place memberships. Covering the union by factor times
representative therefore reduces intersection tests to representative masks.
To test a product, cover x and y⁻¹, obtaining x = q*a and y⁻¹ = q'*b.
Membership of x*y then implies membership of a*b⁻¹ in the same place.
No closure, cardinality or uniqueness property of the factor list is used.

The application is the literal conjugate parabolics of Parrott (1972), §5,
p.683. Concrete data and certificate obligations are in Geometry/Data.lean.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry

/-- Check that every designated parent occurs in the remaining list. -/
def parentCheck {I : Type*} [DecidableEq I] : List I → List I → Bool
  | [_], [] => true
  | _ :: j :: tail, q :: qs =>
      decide (q ∈ j :: tail) && parentCheck (j :: tail) qs
  | _, _ => false

/-- Check all leaf conditions for one representative's support. -/
def rowLeafCheck {I R : Type*} (member : R → I → Bool) (r : R) :
    List I → List I → Bool
  | [_], [] => true
  | i :: j :: tail, q :: qs =>
      (!(member r i && (j :: tail).any (member r)) || member r q) &&
      rowLeafCheck member r (j :: tail) qs
  | _, _ => false

/-- Traverse the large representative list once, keeping only one mask at a time. -/
def leafCheck {I R : Type*} [DecidableEq I] (member : R → I → Bool)
    (rows : List R) (ids parents : List I) : Bool :=
  parentCheck ids parents && rows.all (fun r => rowLeafCheck member r ids parents)

/-- Combine bounded checks without reducing one large certificate in the kernel. -/
theorem all_of_chunk_checks {R : Type*} (test : R → Bool) (width count : Nat)
    (rows : List R) (hsize : rows.length ≤ width * count)
    (hchunks : ∀ k : Fin count,
      ((rows.drop (width * k.val)).take width).all test = true) :
    rows.all test = true := by
  induction count generalizing rows with
  | zero =>
      have he : rows = [] := List.length_eq_zero_iff.mp (by simpa using hsize)
      simp [he]
  | succ count ih =>
      have hfirst : (rows.take width).all test = true := by
        simpa using hchunks 0
      have htail : (rows.drop width).all test = true := by
        apply ih (rows.drop width)
        · simp only [List.length_drop]
          rw [Nat.mul_succ] at hsize
          omega
        · intro k
          have h := hchunks ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
          simpa only [List.drop_drop, Nat.mul_add, Nat.mul_one, Nat.add_comm] using h
      rw [← List.take_append_drop width rows, List.all_append]
      simpa only [Bool.and_eq_true] using And.intro hfirst htail

/-- A factor belonging to a subgroup does not change membership. -/
theorem common_mul_mem_iff {G : Type*} [Group G] (P : Subgroup G)
    {q a : G} (hq : q ∈ P) : q * a ∈ P ↔ a ∈ P := by
  constructor
  · intro h
    simpa only [inv_mul_cancel_left] using P.mul_mem (P.inv_mem hq) h
  · exact P.mul_mem hq

/-- Boolean support checks imply the required leaf intersections. -/
theorem leafIntersections_of_support {G I R : Type*} [Group G] [DecidableEq I]
    (P : I → Subgroup G) (rows : List R) (member : R → I → Bool)
    (ids parents : List I)
    (hsupport : ∀ x : G, (∃ i ∈ ids, x ∈ P i) →
      ∃ r ∈ rows, ∀ i ∈ ids, x ∈ P i ↔ member r i = true)
    (hcheck : leafCheck member rows ids parents = true) :
    LeafIntersections (ids.map P) := by
  simp only [leafCheck, Bool.and_eq_true] at hcheck
  obtain ⟨hshape, hrows⟩ := hcheck
  induction ids generalizing parents with
  | nil => simp [parentCheck] at hshape
  | cons i tail ih =>
      cases tail with
      | nil =>
          cases parents with
          | nil => exact LeafIntersections.singleton (P i)
          | cons q qs => simp [parentCheck] at hshape
      | cons j tail =>
          cases parents with
          | nil => simp [parentCheck] at hshape
          | cons q qs =>
              simp only [parentCheck, Bool.and_eq_true, decide_eq_true_eq] at hshape
              rcases hshape with ⟨hq, htail⟩
              have hrchecks (r : R) (hr : r ∈ rows) := List.all_eq_true.mp hrows r hr
              simp only [rowLeafCheck, Bool.and_eq_true] at hrchecks
              apply LeafIntersections.cons (P i) (P q) ((j :: tail).map P)
              · exact List.mem_map.mpr ⟨q, hq, rfl⟩
              · intro Q hQ x hx
                obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hQ
                obtain ⟨r, hr, hs⟩ := hsupport x ⟨i, List.mem_cons_self, hx.1⟩
                have hi : member r i = true := (hs i List.mem_cons_self).mp hx.1
                have hk' : member r k = true :=
                  (hs k (List.mem_cons_of_mem i hk)).mp hx.2
                have ha : (j :: tail).any (member r) = true :=
                  List.any_eq_true.mpr ⟨k, hk, hk'⟩
                have hq' := (hrchecks r hr).1
                have hm : member r q = true := by
                  simpa only [hi, ha, Bool.true_and, Bool.not_true, Bool.false_or] using hq'
                exact (hs q (List.mem_cons_of_mem i hq)).mpr hm
              · apply ih qs ?_ htail
                  (List.all_eq_true.mpr (fun r hr => (hrchecks r hr).2))
                intro x hx
                obtain ⟨r, hr, hs⟩ := hsupport x (by
                  obtain ⟨k, hk, hx⟩ := hx
                  exact ⟨k, List.mem_cons_of_mem i hk, hx⟩)
                exact ⟨r, hr, fun k hk => hs k (List.mem_cons_of_mem i hk)⟩

/-- A cover by common factors transfers representative supports to the union. -/
theorem union_support_of_common_factors {G I R : Type*} [Group G]
    (P : I → Subgroup G) (ids : List I) (factors : List G)
    (rows : List R) (element : R → G) (member : R → I → Bool)
    (hcommon : ∀ q ∈ factors, ∀ i ∈ ids, q ∈ P i)
    (hcover : ∀ x : G, (∃ i ∈ ids, x ∈ P i) →
      ∃ q ∈ factors, ∃ r ∈ rows, x = q * element r)
    (hmember : ∀ r ∈ rows, ∀ i ∈ ids, element r ∈ P i ↔ member r i = true) :
    ∀ x : G, (∃ i ∈ ids, x ∈ P i) →
      ∃ r ∈ rows, ∀ i ∈ ids, x ∈ P i ↔ member r i = true := by
  intro x hx
  obtain ⟨q, hq, r, hr, rfl⟩ := hcover x hx
  exact ⟨r, hr, fun i hi =>
    (common_mul_mem_iff (P i) (hcommon q hq i hi)).trans (hmember r hr i hi)⟩

/-- Excluding products of representatives with disjoint support is sufficient. -/
theorem productCompatible_of_common_factors {G I R : Type*} [Group G]
    (P : I → Subgroup G) (ids : List I) (factors : List G)
    (rows : List R) (element : R → G) (member : R → I → Bool)
    (hcommon : ∀ q ∈ factors, ∀ i ∈ ids, q ∈ P i)
    (hcover : ∀ x : G, (∃ i ∈ ids, x ∈ P i) →
      ∃ q ∈ factors, ∃ r ∈ rows, x = q * element r)
    (hmember : ∀ r ∈ rows, ∀ i ∈ ids, element r ∈ P i ↔ member r i = true)
    (hproducts : ∀ a ∈ rows, ∀ b ∈ rows,
      ids.any (fun i => member a i && member b i) = false →
      ∀ i ∈ ids, element a * (element b)⁻¹ ∉ P i) :
    ProductCompatible (ids.map P) := by
  intro x y hx hy hxy
  have index_of_mem {z : G} (hz : ∃ Q ∈ ids.map P, z ∈ Q) :
      ∃ i ∈ ids, z ∈ P i := by
    obtain ⟨Q, hQ, hz⟩ := hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hQ
    exact ⟨i, hi, hz⟩
  obtain ⟨q, hq, a, ha, hx⟩ := hcover x (index_of_mem hx)
  obtain ⟨q', hq', b, hb, hyinv⟩ := hcover y⁻¹ (by
    obtain ⟨i, hi, hy⟩ := index_of_mem hy
    exact ⟨i, hi, (P i).inv_mem hy⟩)
  have hy : y = (element b)⁻¹ * q'⁻¹ := by
    simpa only [inv_inv, mul_inv_rev] using congrArg Inv.inv hyinv
  have hshare : ids.any (fun i => member a i && member b i) = true := by
    cases he : ids.any (fun i => member a i && member b i) with
    | true => rfl
    | false =>
        obtain ⟨i, hi, hxy⟩ := index_of_mem hxy
        have helem : element a * (element b)⁻¹ ∈ P i := by
          have h := (P i).mul_mem
            ((P i).mul_mem ((P i).inv_mem (hcommon q hq i hi)) hxy)
            (hcommon q' hq' i hi)
          have hid : q⁻¹ * (x * y) * q' = element a * (element b)⁻¹ := by
            rw [hx, hy]
            group
          rwa [hid] at h
        exact (hproducts a ha b hb he i hi helem).elim
  obtain ⟨i, hi, hm⟩ := List.any_eq_true.mp hshare
  have hm' : member a i = true ∧ member b i = true := by
    simpa only [Bool.and_eq_true] using hm
  refine ⟨P i, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_, ?_⟩
  · rw [hx]
    exact (P i).mul_mem (hcommon q hq i hi) ((hmember a ha i hi).mpr hm'.1)
  · rw [hy]
    exact (P i).mul_mem ((P i).inv_mem ((hmember b hb i hi).mpr hm'.2))
      ((P i).inv_mem (hcommon q' hq' i hi))

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry
