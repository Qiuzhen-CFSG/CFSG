module

public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Index
public import Theory.GroupTheory.PGroup.MaximalIndex
public import Theory.GroupTheory.SubgroupEnumeration
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Binary Schreier certificates for maximal-subgroup enumeration

A maximal subgroup of a finite two-group has relative index two. Its membership
on a generating family is a nonzero binary signature. Choose an outside
generator `t`; the transversal `{1,t}` gives the two Schreier generators for
each original generator. Their closure is exactly the maximal subgroup.

This reduces maximal-subgroup coverage to checks on finitely many explicit
generated subgroups, without enumerating the subgroup lattice. The generating
family need not be minimal and no presentation is assumed. A cyclic special
case says that every maximal subgroup is contained in any subgroup containing
the square of the cyclic generator.

Source: Schreier's lemma (`Subgroup.closure_mul_image_eq` in Mathlib) and the
maximal-index theorem for finite p-groups in `PGroup.MaximalIndex`.
-/

open scoped Pointwise
namespace Theory.GroupTheory.SubgroupEnumeration
variable {G : Type*} [Group G] {ι : Type*}

/-- The two Schreier generators for each original generator. A true signature
marks a generator outside the index-two subgroup. -/
@[expose] public def binarySchreierGenerator (s : ι → G) (t : G) (σ : ι → Bool) : Bool × ι → G
  | (false, i) => if σ i then s i * t⁻¹ else s i
  | (true, i) => if σ i then t * s i else t * s i * t⁻¹

private theorem binarySchreier_eq (H : Subgroup G) (hi : H.index = 2)
    (s : ι → G) (hs : Subgroup.closure (Set.range s) = ⊤)
    (t : G) (ht : t ∉ H) (σ : ι → Bool)
    (hσ : ∀ i, σ i = true ↔ s i ∉ H) :
    Subgroup.closure (Set.range (binarySchreierGenerator s t σ)) = H := by
  classical
  have hc : Subgroup.IsComplement (H : Set G) ({1, t} : Set G) := by
    apply Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mpr
    intro x
    by_cases hx : x ∈ H
    · refine ⟨⟨1, by simp⟩, by simpa using hx, ?_⟩
      rintro ⟨r, hr⟩ hmem
      apply Subtype.ext
      rcases hr with hr | hr
      · exact hr
      · have he : r = t := hr
        subst r
        have : t⁻¹ ∈ H := (H.mul_mem_cancel_left hx).mp hmem
        exact (ht (H.inv_mem_iff.mp this)).elim
    · refine ⟨⟨t, by simp⟩, ?_, ?_⟩
      · exact (H.mul_mem_iff_of_index_two hi).mpr (by simpa using (iff_of_false hx ht))
      · rintro ⟨r, hr⟩ hmem
        apply Subtype.ext
        rcases hr with hr | hr
        · subst r
          exact (hx (by simpa using hmem)).elim
        · exact hr
  have hrep (x : G) : (hc.toRightFun x : G) = if x ∈ H then 1 else t := by
    have hm := hc.mul_inv_toRightFun_mem x
    have hr := (hc.toRightFun x).property
    by_cases hx : x ∈ H
    · rw [if_pos hx]
      rcases hr with hr | hr
      · exact hr
      · have he : (hc.toRightFun x : G) = t := hr
        rw [he] at hm
        exact (ht (H.inv_mem_iff.mp ((H.mul_mem_cancel_left hx).mp hm))).elim
    · rw [if_neg hx]
      rcases hr with hr | hr
      · have he : (hc.toRightFun x : G) = 1 := hr
        rw [he] at hm
        exact (hx (by simpa using hm)).elim
      · exact hr
  rw [← Subgroup.closure_mul_image_eq hc (by simp) hs]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨b, i⟩, rfl⟩
    cases b
    · refine ⟨s i, ⟨1, by simp, s i, ⟨i, rfl⟩, one_mul _⟩, ?_⟩
      dsimp only
      rw [hrep]
      by_cases h : s i ∈ H
      · have hh : σ i = false := Bool.eq_false_iff.mpr (by simpa [h] using (hσ i).mp)
        simp [binarySchreierGenerator, h, hh]
      · have hh := (hσ i).mpr h
        simp [binarySchreierGenerator, h, hh]
    · refine ⟨t * s i, ⟨t, by simp, s i, ⟨i, rfl⟩, rfl⟩, ?_⟩
      dsimp only
      rw [hrep, H.mul_mem_iff_of_index_two hi]
      by_cases h : s i ∈ H
      · have hh : σ i = false := Bool.eq_false_iff.mpr (by simpa [h] using (hσ i).mp)
        simp [binarySchreierGenerator, h, ht, hh]
      · have hh := (hσ i).mpr h
        simp [binarySchreierGenerator, h, ht, hh]
  · rintro ⟨y, ⟨r, hr, _, ⟨i, rfl⟩, rfl⟩, rfl⟩
    rcases hr with hr | hr
    · have he : r = 1 := hr
      subst r
      refine ⟨(false, i), ?_⟩
      dsimp only
      rw [one_mul, hrep]
      by_cases h : s i ∈ H
      · have hh : σ i = false := Bool.eq_false_iff.mpr (by simpa [h] using (hσ i).mp)
        simp [binarySchreierGenerator, h, hh]
      · have hh := (hσ i).mpr h
        simp [binarySchreierGenerator, h, hh]
    · have he : r = t := hr
      subst r
      refine ⟨(true, i), ?_⟩
      dsimp only
      rw [hrep, H.mul_mem_iff_of_index_two hi]
      by_cases h : s i ∈ H
      · have hh : σ i = false := Bool.eq_false_iff.mpr (by simpa [h] using (hσ i).mp)
        simp [binarySchreierGenerator, h, ht, hh]
      · have hh := (hσ i).mpr h
        simp [binarySchreierGenerator, h, ht, hh]

/-- A maximal step inside a subgroup of a finite two-group has relative index two. -/
public theorem relIndex_two_of_covBy [Finite G] (hG : IsPGroup 2 G)
    {H K : Subgroup G} (h : H ⋖ K) : H.relIndex K = 2 := by
  apply (hG.to_subgroup K).index_of_isCoatom
  refine ⟨?_, ?_⟩
  · intro he
    exact h.ne (le_antisymm h.le (Subgroup.subgroupOf_eq_top.mp he))
  · intro L hL
    have hHL : H < L.map K.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.le]
      exact Subgroup.map_subtype_lt_map_subtype.mpr hL
    have he : L.map K.subtype = K := (h.eq_or_eq hHL.le (Subgroup.map_subtype_le L)).resolve_left hHL.ne'
    apply Subgroup.map_injective K.subtype_injective
    simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using he

/-- The actual binary membership signature recovers an index-two subgroup by
explicit Schreier generators in the ambient group. -/
public theorem binarySchreier_eq_relative {H K : Subgroup G} (hHK : H ≤ K)
    (hi : H.relIndex K = 2)
    (s : ι → G) (hs : Subgroup.closure (Set.range s) = K)
    (t : G) (htK : t ∈ K) (ht : t ∉ H) (σ : ι → Bool)
    (hσ : ∀ i, σ i = true ↔ s i ∉ H) :
    Subgroup.closure (Set.range (binarySchreierGenerator s t σ)) = H := by
  let s' : ι → K := fun i => ⟨s i, hs ▸ Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hs' : Subgroup.closure (Set.range s') = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    change Subgroup.closure (Set.range s) = K
    exact hs
  have he := binarySchreier_eq (H.subgroupOf K) hi s' hs' ⟨t, htK⟩ ht σ hσ
  have hm := congrArg (Subgroup.map K.subtype) he
  rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_subgroupOf_eq_of_le hHK] at hm
  have hfun : K.subtype ∘ binarySchreierGenerator s' ⟨t, htK⟩ σ =
      binarySchreierGenerator s t σ := by
    funext ⟨b, i⟩
    cases b <;> cases hh : σ i <;> simp [binarySchreierGenerator, hh, s']
  rw [hfun] at hm
  exact hm

/-- Every maximal subgroup of a finite two-group has a binary Schreier description. -/
public theorem exists_binarySchreier_of_covBy [Finite G] (hG : IsPGroup 2 G)
    {H K : Subgroup G} (h : H ⋖ K)
    (s : ι → G) (hs : Subgroup.closure (Set.range s) = K) :
    ∃ (σ : ι → Bool) (j : ι), σ j = true ∧
      Subgroup.closure (Set.range (binarySchreierGenerator s (s j) σ)) = H := by
  classical
  have hj : ∃ j, s j ∉ H := by
    by_contra hh
    push Not at hh
    have : K ≤ H := by
      rw [← hs, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hh i
    exact h.lt.not_ge this
  obtain ⟨j, hj⟩ := hj
  let σ : ι → Bool := fun i => decide (s i ∉ H)
  have hσ : ∀ i, σ i = true ↔ s i ∉ H := fun i => by simp [σ]
  refine ⟨σ, j, (hσ j).mpr hj, ?_⟩
  exact binarySchreier_eq_relative h.le (relIndex_two_of_covBy hG h)
    s hs (s j) (hs ▸ Subgroup.subset_closure ⟨j, rfl⟩) hj σ hσ


/-- A maximal subgroup of a cyclic subgroup of a finite two-group is contained
in any subgroup containing the square of its generator. -/
public theorem le_of_covBy_cyclic [Finite G] (hG : IsPGroup 2 G)
    (t : G) {H N : Subgroup G} (h : H ⋖ Subgroup.closure {t})
    (ht : t * t ∈ N) : H ≤ N := by
  let s : Unit → G := fun _ => t
  have hs : Subgroup.closure (Set.range s) = Subgroup.closure {t} := by
    congr 1
    ext x
    simp [s]
  obtain ⟨σ, j, hj, he⟩ := exists_binarySchreier_of_covBy hG h s hs
  rw [← he, Subgroup.closure_le]
  rintro _ ⟨⟨b, i⟩, rfl⟩
  have hi : σ i = true := by simpa only [show i = j from Subsingleton.elim _ _] using hj
  cases b
  · simp [binarySchreierGenerator, hi, s]
  · simpa [binarySchreierGenerator, hi, s] using ht

/-- Binary Schreier branch certificates imply maximal-step coverage outside a
fixed subgroup. Noncentric branches are excluded by an actual outside
centralizer element; no unrelated local exclusion is used in the descent. -/
public theorem represented_of_binary_checks [Finite G] (hG : IsPGroup 2 G)
    {κ : Type*} (K : κ → Subgroup G) (E : Subgroup G)
    (i : κ) (s : ι → G) (hs : Subgroup.closure (Set.range s) = K i)
    (hcheck : ∀ (σ : ι → Bool) (j : ι), σ j = true →
      let L := Subgroup.closure (Set.range (binarySchreierGenerator s (s j) σ))
      L ≤ E ∨ (∃ g, g ∈ Subgroup.centralizer (L : Set G) ∧ g ∉ L) ∨ Represented K L)
    (H : Subgroup G) (hmax : H ⋖ K i)
    (hcent : Subgroup.centralizer (H : Set G) ≤ H)
    (hE : ¬ H ≤ E) : Represented K H := by
  obtain ⟨σ, j, hj, he⟩ := exists_binarySchreier_of_covBy hG hmax s hs
  have hc := hcheck σ j hj
  dsimp only at hc
  rw [he] at hc
  rcases hc with hp | ⟨g, hg, hng⟩ | hr
  · exact (hE hp).elim
  · exact (hng (hcent hg)).elim
  · exact hr

end Theory.GroupTheory.SubgroupEnumeration
