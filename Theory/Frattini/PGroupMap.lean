module
public import Theory.Frattini.PGroup

/-!
# Frattini subgroups under homomorphisms of finite p-groups

Every homomorphism between finite p-groups maps the source Frattini subgroup
into the target Frattini subgroup. Surjectivity is not required: the description
of the Frattini subgroup by commutators and p-th powers makes this immediate,
since homomorphisms preserve both kinds of generators.

This standard finite-group fact supports the two-group Frattini comparison in
Stellmacher, *Pushing up*, Arch. Math. 46 (1986), proof of (3.4)(b), p.16.
The mathematical input is the generator description in `Theory.Frattini.PGroup`.
-/

/-- Homomorphisms of finite p-groups map Frattini elements to Frattini elements. -/
public theorem frattini_map_le_of_isPGroup
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)] [Fact (IsPGroup p H)]
    (f : G →* H) : (frattini G).map f ≤ frattini H := by
  rw [Subgroup.map_le_iff_le_comap, frattini_eq_closure_commutator_union_powers (p := p)]
  apply (Subgroup.closure_le (K := (frattini H).comap f)).mpr
  rintro x (hx | ⟨y, rfl⟩)
  · have hm : (commutator G).map f ≤ commutator H := by
      rw [map_commutator_eq, commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact commutator_le_frattini_of_isPGroup (p := p)
      (hm (Subgroup.mem_map_of_mem f hx))
  · change f (y ^ p) ∈ frattini H
    rw [map_pow]
    exact pth_power_mem_frattini_of_isPGroup (p := p) (f y)
