module

public import Theory.GroupAction.EvenPolygonFixedPoints

/-!
# Canonical stabilizers from colored fixed trees

The invariant center of a finite two-colored tree is fixed by every
color-preserving automorphism. Applied to the vertices fixed by a subgroup,
this selects a vertex whose stabilizer contains the subgroup normalizer and
is preserved by every subgroup-preserving semilinear graph symmetry.

The simultaneous invariance clause is used for rank-two building escapes:
it preserves the original external stabilizer when selecting a parabolic.
Source: the finite-building proof of Borel--Tits, GLS3 Theorem 3.1.3;
Aschbacher--Smith 2.4.25, printed p.543.
-/

@[expose] public section

namespace GroupAction.EvenPolygon

variable {G X : Type*} [Group G] [MulAction G X]
variable {Γ : SimpleGraph X} {color : X → Bool}

private theorem map_mem_fixed (R : Subgroup G) (a : MulAut G)
    (ha : R.map a.toMonoidHom = R) (f : Γ ≃g Γ)
    (hf : ∀ g x, f (g • x) = a g • f x)
    {x : X} (hx : x ∈ fixedVertices R) : f x ∈ fixedVertices R := by
  intro r hr
  rw [← ha] at hr
  obtain ⟨s, hs, rfl⟩ := hr
  exact (hf s x).symm.trans (congrArg f (hx s hs))

private theorem symm_mem_fixed (R : Subgroup G) (a : MulAut G)
    (ha : R.map a.toMonoidHom = R) (f : Γ ≃g Γ)
    (hf : ∀ g x, f (g • x) = a g • f x)
    {x : X} (hx : x ∈ fixedVertices R) : f.symm x ∈ fixedVertices R := by
  intro r hr
  apply f.injective
  rw [hf, f.apply_symm_apply]
  exact hx (a r) (ha ▸ Subgroup.mem_map.mpr ⟨r, hr, rfl⟩)

/-- The center of a two-colored fixed tree selects one vertex simultaneously
for every type-preserving semilinear symmetry stabilizing the subgroup. -/
theorem fixed_tree_invariant_vertex [Finite X] (R : Subgroup G)
    (hT : (Γ.induce (fixedVertices R)).IsTree)
    (hcol : ∀ {x y}, Γ.Adj x y → color x ≠ color y) :
    ∃ v : X, v ∈ fixedVertices R ∧
      ∀ (a : MulAut G), R.map a.toMonoidHom = R →
        ∀ (f : Γ ≃g Γ), (∀ g x, f (g • x) = a g • f x) →
          (∀ x, color (f x) = color x) → f v = v := by
  obtain ⟨v, hv⟩ := hT.exists_fixed_vertex_of_color_preserving
    (fun x => color x.val) (fun h => hcol h)
  refine ⟨v.val, v.property, ?_⟩
  intro a ha f hf hc
  let fR : Γ.induce (fixedVertices R) ≃g Γ.induce (fixedVertices R) :=
    { toEquiv :=
        { toFun := fun x => ⟨f x, map_mem_fixed R a ha f hf x.property⟩
          invFun := fun x => ⟨f.symm x, symm_mem_fixed R a ha f hf x.property⟩
          left_inv := fun x => Subtype.ext (f.symm_apply_apply x)
          right_inv := fun x => Subtype.ext (f.apply_symm_apply x) }
      map_rel_iff' := by intro x y; exact f.map_rel_iff }
  exact congrArg Subtype.val (hv fR (fun x => hc x.val))

/-- Semilinear fixation of a vertex gives literal invariance of its stabilizer. -/
theorem stabilizer_map_eq_of_semilinear_fixed (a : MulAut G) (f : X ≃ X)
    (hf : ∀ g x, f (g • x) = a g • f x) (v : X) (hv : f v = v) :
    (MulAction.stabilizer G v).map a.toMonoidHom = MulAction.stabilizer G v := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    change a g • v = v
    rw [← hv, ← hf, show g • v = v from hg]
  · intro g hg
    refine Subgroup.mem_map.mpr ⟨a.symm g, ?_, a.apply_symm_apply g⟩
    change a.symm g • v = v
    apply f.injective
    rw [hf, a.apply_symm_apply, hv]
    exact hg

/-- A canonical fixed-tree vertex has a normalizer-containing stabilizer which
is invariant under every subgroup-preserving automorphism admitting a colored
semilinear action on the graph. -/
theorem fixed_tree_invariant_stabilizer [Finite X] (R : Subgroup G)
    (hT : (Γ.induce (fixedVertices R)).IsTree)
    (hcol : ∀ {x y}, Γ.Adj x y → color x ≠ color y)
    (hsmul : ∀ (g : G) {x y}, Γ.Adj x y → Γ.Adj (g • x) (g • y))
    (hcsmul : ∀ (g : G) x, color (g • x) = color x) :
    ∃ v : X,
      Subgroup.normalizer (R : Set G) ≤ MulAction.stabilizer G v ∧
      ∀ (a : MulAut G), R.map a.toMonoidHom = R →
        (∃ f : Γ ≃g Γ, (∀ g x, f (g • x) = a g • f x) ∧
          ∀ x, color (f x) = color x) →
        (MulAction.stabilizer G v).map a.toMonoidHom = MulAction.stabilizer G v := by
  obtain ⟨v, _, hv⟩ := fixed_tree_invariant_vertex R hT hcol
  refine ⟨v, ?_, ?_⟩
  · intro n hn
    let f : Γ ≃g Γ :=
      { toEquiv := MulAction.toPerm n
        map_rel_iff' := by
          intro x y
          constructor
          · intro h
            simpa only [MulAction.toPerm_apply, inv_smul_smul] using hsmul n⁻¹ h
          · exact hsmul n }
    have ha : R.map (MulAut.conj n).toMonoidHom = R := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hn y).mp hy
      · intro hx
        refine ⟨n⁻¹ * x * n, ?_, ?_⟩
        · change n⁻¹ * x * n ∈ R
          simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (R : Set G)).inv_mem hn) x).mp hx
        · simp [mul_assoc]
    apply hv (MulAut.conj n) ha f
    · intro g x
      change n • (g • x) = (n * g * n⁻¹) • (n • x)
      simp [mul_smul]
    · exact hcsmul n
  · intro a ha ⟨f, hf, hc⟩
    exact stabilizer_map_eq_of_semilinear_fixed a f.toEquiv hf v (hv a ha f hf hc)

end GroupAction.EvenPolygon
