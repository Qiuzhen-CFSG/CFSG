module

public import Theory.AlgebraicGroup.BNPair.StandardParabolicCore
public import Theory.GroupAction.TypedCosetGeometry
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# The coset geometry of a marked octagonal Tits system

The vertices and group action are the typed parabolic cosets. The apartment is
exactly the normalizer orbit of the standard vertices. `OctagonalDatum` marks
the two simple reflections in the actual Weyl quotient and identifies the
vertex subgroups; it contains no metric or apartment-conjugacy assumptions.

Bruhat decomposition places any two chambers in a common translated apartment.
Bruhat-index uniqueness and standard-parabolic saturation identify precisely
when two normalizer representatives give the same vertex. These are the
algebraic inputs to the rank-two building argument.

Source: the BN-pair construction in GLS3 §§2.3 and 2.6,
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section

namespace Theory.AlgebraicGroup.TitsSystem.DihedralGeometry

open Subgroup
open scoped Pointwise

variable {X I : Type*} [Group X]

/-- The incidence graph of a typed family of left cosets. -/
def graph (F : I → Subgroup X) : SimpleGraph (CosetGeometry.Vertex F) where
  Adj v w := v.type ≠ w.type ∧ CosetGeometry.Incident F v w
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm F⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The actual normalizer apartment in the coset action. -/
def apartment (T : TitsSystem (X := X)) (F : I → Subgroup X) :
    Set (CosetGeometry.Vertex F) :=
  {v | ∃ n ∈ T.N, ∃ i : I, n • CosetGeometry.base F i = v}

/-- The standard normalizer orbit is the support of a simple sixteen-cycle. -/
def StandardApartmentCycle (T : TitsSystem (X := X)) (F : I → Subgroup X) : Prop :=
  ∃ v, ∃ p : (graph F).Walk v v,
    p.IsCycle ∧ p.length = 16 ∧ {w | w ∈ p.support} = apartment T F

/-- Algebraic marking of an octagonal Weyl quotient and its two parabolics. -/
structure OctagonalDatum (T : TitsSystem (X := X)) (F : I → Subgroup X) where
  typeEquiv : I ≃ Bool
  simple : I → (T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N)
  simple_range : Set.range simple = T.S
  weylEquiv : (T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) ≃* DihedralGroup 8
  map_simple : ∀ i, weylEquiv (simple i) =
    DihedralGroup.sr (if typeEquiv i then 1 else 0)
  parabolic_eq : ∀ i, F i = T.standardParabolic {simple i}

variable (F : I → Subgroup X)

/-- Incidence retains the simultaneous group representative of both vertices. -/
theorem incident_iff_common_translate (v w : CosetGeometry.Vertex F) :
    CosetGeometry.Incident F v w ↔ ∃ g : X,
      g • CosetGeometry.base F v.type = v ∧
      g • CosetGeometry.base F w.type = w := by
  have hrep (g : X) (v : CosetGeometry.Vertex F) :
      (g : X ⧸ F v.type) = v.coset ↔ g • CosetGeometry.base F v.type = v := by
    rcases v with ⟨i, q⟩
    change _ ↔ CosetGeometry.Vertex.mk i (g • ((1 : X) : X ⧸ F i)) = _
    simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
      CosetGeometry.Vertex.mk.injEq, heq_eq_eq, true_and]
  simp only [CosetGeometry.Incident, hrep]

/-- Left translation is a graph automorphism, here exposed as a homomorphism. -/
def smulHom (g : X) : graph F →g graph F where
  toFun := (g • ·)
  map_rel' h := ⟨h.1, h.2.smul F g⟩

@[simp] theorem smulHom_apply (g : X) (v : CosetGeometry.Vertex F) :
    smulHom F g v = g • v := rfl

/-- Equality of left-translated standard vertices has the usual inverse-left
coset convention. -/
theorem smul_base_eq_iff (g h : X) (i : I) :
    g • CosetGeometry.base F i = h • CosetGeometry.base F i ↔ g⁻¹ * h ∈ F i := by
  rw [← CosetGeometry.stabilizer_base F i, MulAction.mem_stabilizer_iff, mul_smul]
  constructor
  · intro he
    rw [← he, inv_smul_smul]
  · intro he
    simpa only [smul_inv_smul] using (congrArg (g • ·) he).symm

variable (T : TitsSystem (X := X))

@[simp] theorem base_mem_apartment (i : I) : CosetGeometry.base F i ∈ apartment T F :=
  ⟨1, T.N.one_mem, i, one_smul _ _⟩

/-- Elements of the chamber subgroup fix every standard vertex. -/
theorem borel_fixes_base (hB : ∀ i, T.B ≤ F i) {b : X} (hb : b ∈ T.B) (i : I) :
    b • CosetGeometry.base F i = CosetGeometry.base F i := by
  apply MulAction.mem_stabilizer_iff.mp
  rw [CosetGeometry.stabilizer_base]
  exact hB i hb

/-- Any two translates of the standard chamber are contained in a common
translate of the normalizer apartment. -/
theorem exists_apartment_for_chambers (hB : ∀ i, T.B ≤ F i) (g h : X) :
    ∃ k : X, (∀ i, g • CosetGeometry.base F i ∈ k • apartment T F) ∧
      (∀ i, h • CosetGeometry.base F i ∈ k • apartment T F) := by
  obtain ⟨w, z, ⟨b, hb, n, ⟨nN, hn, rfl⟩, rfl⟩, c, hc, he⟩ :=
    T.exists_mem_doubleCoset (g⁻¹ * h)
  have hfactor : h = g * b * (nN : X) * c := by
    calc
      h = g * (g⁻¹ * h) := (mul_inv_cancel_left g h).symm
      _ = g * (b * (nN : X) * c) := congrArg (g * ·) he.symm
      _ = _ := by simp only [mul_assoc]
  refine ⟨g * b, ?_, ?_⟩
  · intro i
    have hv := Set.smul_mem_smul_set (a := g * b) (base_mem_apartment F T i)
    simpa only [mul_smul, borel_fixes_base F T hB hb] using hv
  · intro i
    have hnA : (nN : X) • CosetGeometry.base F i ∈ apartment T F :=
      ⟨nN, nN.property, i, rfl⟩
    have hv := Set.smul_mem_smul_set (a := g * b) hnA
    rw [hfactor]
    simpa only [mul_smul, borel_fixes_base F T hB hc] using hv

/-- In particular, any two edges are contained in a common actual apartment
translate. The incidence graph and group action are unchanged. -/
theorem exists_apartment_for_edges (hB : ∀ i, T.B ≤ F i)
    {v₁ v₂ w₁ w₂ : CosetGeometry.Vertex F}
    (hv : (graph F).Adj v₁ v₂) (hw : (graph F).Adj w₁ w₂) :
    ∃ k : X, v₁ ∈ k • apartment T F ∧ v₂ ∈ k • apartment T F ∧
      w₁ ∈ k • apartment T F ∧ w₂ ∈ k • apartment T F := by
  obtain ⟨g, hg₁, hg₂⟩ := (incident_iff_common_translate F v₁ v₂).mp hv.2
  obtain ⟨h, hh₁, hh₂⟩ := (incident_iff_common_translate F w₁ w₂).mp hw.2
  obtain ⟨k, hkg, hkh⟩ := exists_apartment_for_chambers F T hB g h
  exact ⟨k, hg₁ ▸ hkg _, hg₂ ▸ hkg _, hh₁ ▸ hkh _, hh₂ ▸ hkh _⟩

/-- The same Bruhat argument places any two vertices in a common apartment. -/
theorem exists_apartment_for_vertices (hB : ∀ i, T.B ≤ F i)
    (v w : CosetGeometry.Vertex F) :
    ∃ k : X, v ∈ k • apartment T F ∧ w ∈ k • apartment T F := by
  obtain ⟨g, hg⟩ := CosetGeometry.exists_smul_base F v
  obtain ⟨h, hh⟩ := CosetGeometry.exists_smul_base F w
  obtain ⟨k, hkg, hkh⟩ := exists_apartment_for_chambers F T hB g h
  exact ⟨k, hg ▸ hkg _, hh ▸ hkh _⟩

/-- Once the normalizer orbit is a sixteen-cycle, Bruhat coverage gives the
required diameter bound on the entire coset graph. -/
theorem diameter_bound_of_standardApartmentCycle (hB : ∀ i, T.B ≤ F i)
    (hA : StandardApartmentCycle T F) (v w : CosetGeometry.Vertex F) :
    ∃ p : (graph F).Walk v w, p.length ≤ 8 := by
  classical
  obtain ⟨k, hv, hw⟩ := exists_apartment_for_vertices F T hB v w
  obtain ⟨v', hv', rfl⟩ := Set.mem_smul_set.mp hv
  obtain ⟨w', hw', rfl⟩ := Set.mem_smul_set.mp hw
  obtain ⟨a, c, _, hlen, hsupp⟩ := hA
  rw [← hsupp] at hv' hw'
  let q := c.rotate v' hv'
  have hwq : w' ∈ q.support := by
    exact (c.mem_support_rotate_iff v' hv').mpr hw'
  have hsum : (q.takeUntil w' hwq).length + (q.dropUntil w' hwq).length = 16 := by
    rw [← SimpleGraph.Walk.length_append, q.take_spec hwq]
    simpa only [q, SimpleGraph.Walk.length_rotate] using hlen
  have hshort : ∃ p : (graph F).Walk v' w', p.length ≤ 8 := by
    by_cases hle : (q.takeUntil w' hwq).length ≤ 8
    · exact ⟨q.takeUntil w' hwq, hle⟩
    · refine ⟨(q.dropUntil w' hwq).reverse, ?_⟩
      rw [SimpleGraph.Walk.length_reverse]
      omega
  obtain ⟨p, hp⟩ := hshort
  refine ⟨(p.map (smulHom F k)).copy (smulHom_apply F k v') (smulHom_apply F k w'), ?_⟩
  simpa only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map] using hp

variable {F T}

namespace OctagonalDatum

variable (D : OctagonalDatum T F)

theorem simple_mem (i : I) : D.simple i ∈ T.S := by
  rw [← D.simple_range]
  exact ⟨i, rfl⟩

include D in
theorem borel_le (i : I) : T.B ≤ F i := by
  rw [D.parabolic_eq]
  exact T.B_le_standardParabolic _

/-- Distinct vertex types have distinct marked simple reflections. -/
theorem simple_injective : Function.Injective D.simple := by
  intro i j hij
  apply D.typeEquiv.injective
  have h := congrArg D.weylEquiv hij
  rw [D.map_simple, D.map_simple] at h
  cases hi : D.typeEquiv i <;> cases hj : D.typeEquiv j <;> simp_all
  all_goals exact absurd h (by decide)

/-- The rank-one Weyl subgroup contains exactly the identity and its marked
reflection. -/
theorem mem_closure_simple_iff (i : I)
    (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) :
    w ∈ closure ({D.simple i} : Set _) ↔ w = 1 ∨ w = D.simple i := by
  constructor
  · intro hw
    have hs2 := (T.involutions _ (D.simple_mem i)).2
    induction hw using Subgroup.closure_induction with
    | mem x hx => exact Or.inr (Set.mem_singleton_iff.mp hx)
    | one => exact Or.inl rfl
    | mul a b ha hb iha ihb =>
      rcases iha with rfl | rfl <;> rcases ihb with rfl | rfl
      all_goals simp_all [pow_two]
    | inv a ha iha =>
      rcases iha with rfl | rfl
      all_goals simp_all [pow_two, mul_eq_one_iff_inv_eq]
  · rintro (rfl | rfl)
    · exact (closure _).one_mem
    · exact subset_closure (Set.mem_singleton _)

/-- The vertex subgroup is precisely the union of its two Bruhat cells. -/
theorem mem_parabolic_iff (i : I) (x : X) :
    x ∈ F i ↔ x ∈ T.B ∨ x ∈ T.bruhatCell (D.simple i) := by
  rw [D.parabolic_eq, T.mem_standardParabolic_iff
    (Set.singleton_subset_iff.mpr (D.simple_mem i))]
  simp only [D.mem_closure_simple_iff, or_and_right, exists_or, exists_eq_left, T.bruhatCell_one]
  rfl

include D in
/-- The stabilizer of a standard chamber is exactly the Borel subgroup. -/
theorem parabolic_inf_eq_borel (i j : I) (hne : i ≠ j) : F i ⊓ F j = T.B := by
  apply le_antisymm
  · intro x hx
    rcases (D.mem_parabolic_iff i x).mp hx.1 with h | h
    · exact h
    rcases (D.mem_parabolic_iff j x).mp hx.2 with h' | h'
    · exact h'
    exact (hne (D.simple_injective (T.doubleCoset_index_unique h h'))).elim
  · exact le_inf (D.borel_le i) (D.borel_le j)

/-- A normalizer representative belongs to a vertex subgroup exactly when
its Weyl class belongs to the corresponding rank-one subgroup. -/
theorem representative_mem_parabolic_iff (i : I) (n : T.N) :
    (n : X) ∈ F i ↔
      QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n = 1 ∨
      QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n = D.simple i := by
  have hn := T.representative_mem_bruhatCell _ n rfl
  rw [D.mem_parabolic_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (T.doubleCoset_index_unique hn (by
        change (n : X) ∈ T.bruhatCell 1
        rwa [T.bruhatCell_one]))
    · exact Or.inr (T.doubleCoset_index_unique hn h)
  · rintro (h | h)
    · exact Or.inl (by simpa [h] using hn)
    · exact Or.inr (by simpa [h] using hn)

/-- Equality of apartment vertices is tested in the marked dihedral quotient,
with the inverse-left convention for the genuine left cosets. -/
theorem normalizer_smul_base_eq_iff (i : I) (n n' : T.N) :
    (n : X) • CosetGeometry.base F i = (n' : X) • CosetGeometry.base F i ↔
      D.weylEquiv (QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) (n⁻¹ * n')) = 1 ∨
      D.weylEquiv (QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) (n⁻¹ * n')) =
        DihedralGroup.sr (if D.typeEquiv i then 1 else 0) := by
  rw [smul_base_eq_iff]
  change (↑(n⁻¹ * n') : X) ∈ F i ↔ _
  rw [D.representative_mem_parabolic_iff]
  rw [← D.map_simple i, ← D.weylEquiv.map_one, D.weylEquiv.injective.eq_iff,
    D.weylEquiv.injective.eq_iff]

end OctagonalDatum
end Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
