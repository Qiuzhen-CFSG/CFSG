module

public import Theory.Representation.BinaryNaturalDual.Action
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic

/-!
# Quadratic forms and vector orbits in the binary natural-plus-dual model

A rank-one transvection moves any nonzero covector to another with the same
value at a marked vector. Combined with transitivity on nonzero natural
vectors, this proves inner transitivity on both diagonal classes. The graph
operator joins the two pure classes. These give the exact three nonzero-vector
orbits for any `CoordinateAction` in dimensions four and five.

For uniqueness of the invariant quadratic form, its values on mixed vectors
are the polar pairing of the pure components. Transvections force this pairing
to vanish when evaluation vanishes. Transitivity on evaluation-one pairs and
nondegeneracy then force its remaining value to be one.

These results take the specified actual automorphism action explicitly. They do
not construct that extension, identify an arbitrary source module with it, or
assert the Sylow characterization of the singular diagonal class.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1(1–2),
printed pp.389–390. The Sylow clause has an existential quantifier.
-/

@[expose] public section

open scoped CharTwo
namespace BinaryNaturalDual.ModelOrbits
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem binary_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha

private theorem exists_apply_one {f : Module.Dual (ZMod 2) V} (hf : f ≠ 0) :
    ∃ x, f x = 1 := by
  have hn : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext h)
  obtain ⟨x, hx⟩ := hn
  exact ⟨x, binary_one hx⟩

private theorem exists_common_one {f k : Module.Dual (ZMod 2) V}
    (hf : f ≠ 0) (hk : k ≠ 0) : ∃ x, f x = 1 ∧ k x = 1 := by
  obtain ⟨x, hx⟩ := exists_apply_one hf
  obtain ⟨y, hy⟩ := exists_apply_one hk
  by_cases hkx : k x = 0
  · by_cases hfy : f y = 0
    · exact ⟨x + y, by simp [hx, hfy], by simp [hkx, hy]⟩
    · exact ⟨y, binary_one hfy, hy⟩
  · exact ⟨x, hx, binary_one hkx⟩

/-- A point stabilizer moves any nonzero covector to any other with the same value there. -/
theorem exists_fixing_vector_dual_eq {x : V} {f k : Module.Dual (ZMod 2) V}
    (hf : f ≠ 0) (hk : k ≠ 0) (h : f x = k x) :
    ∃ g : BinaryLinear.GL V, g x = x ∧ g.symm.dualMap f = k := by
  obtain ⟨z, hfz, hkz⟩ := exists_common_one hf hk
  have hd : (f + k) z = 0 := by simp [hfz, hkz]
  refine ⟨BinaryLinear.transvection z (f + k) hd, ?_, ?_⟩
  · change x + (f + k) x • z = x
    simp [h]
  · ext w
    change f (w + (f + k) w • z) = k w
    simp [hfz]

/-- The linear group is transitive on pairs of nonzero components with a fixed pairing. -/
theorem exists_naturalDual_eq [FiniteDimensional (ZMod 2) V]
    {v w : Space V} (hv : v.1 ≠ 0) (hw : w.1 ≠ 0)
    (hv' : v.2 ≠ 0) (hw' : w.2 ≠ 0) (h : quadratic v = quadratic w) :
    ∃ g : BinaryLinear.GL V, naturalDualRepresentation g v = w := by
  obtain ⟨a, ha⟩ := BinaryLinear.OuterCyclic.exists_linearEquiv_apply_eq hv hw
  have hfa : a.symm.dualMap v.2 ≠ 0 := by simpa using hv'
  have he : (a.symm.dualMap v.2) w.1 = w.2 w.1 := by
    change v.2 (a.symm w.1) = w.2 w.1
    rw [show a.symm w.1 = v.1 by rw [← ha, a.symm_apply_apply]]
    exact h
  obtain ⟨b, hb, hb'⟩ := exists_fixing_vector_dual_eq hfa hw' he
  refine ⟨b * a, ?_⟩
  rw [map_mul]
  change naturalDualRepresentation b (naturalDualRepresentation a v) = w
  simp only [naturalDualRepresentation_apply, ha, hb]
  exact Prod.ext rfl hb'

theorem exists_naturalDual_eq_of_pairing_one [FiniteDimensional (ZMod 2) V]
    {v w : Space V} (hv : quadratic v = 1) (hw : quadratic w = 1) :
    ∃ g : BinaryLinear.GL V, naturalDualRepresentation g v = w := by
  apply exists_naturalDual_eq (h := hv.trans hw.symm)
  · intro h; simp [quadratic_apply, h] at hv
  · intro h; simp [quadratic_apply, h] at hw
  · intro h; simp [quadratic_apply, h] at hv
  · intro h; simp [quadratic_apply, h] at hw

private theorem quadratic_cross (Q : QuadraticForm (ZMod 2) (Space V))
    (h₁ : ∀ x, Q (x, 0) = 0) (h₂ : ∀ f, Q (0, f) = 0)
    (x : V) (f : Module.Dual (ZMod 2) V) :
    Q (x, f) = Q.polarBilin (x, 0) (0, f) := by
  simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h₁, h₂]

private theorem quadratic_cross_add (Q : QuadraticForm (ZMod 2) (Space V))
    (h₁ : ∀ x, Q (x, 0) = 0) (h₂ : ∀ f, Q (0, f) = 0)
    (x : V) (f k : Module.Dual (ZMod 2) V) :
    Q (x, f + k) = Q (x, f) + Q (x, k) := by
  simp only [quadratic_cross Q h₁ h₂]
  simpa only [Prod.mk_add_mk, zero_add] using
    map_add (Q.polarBilin (x, 0)) (0, f) (0, k)

/-- Inner invariance and singular summands force every orthogonal mixed vector to be singular. -/
theorem quadratic_zero_of_pairing_zero [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) (Space V))
    (h₁ : ∀ x, Q (x, 0) = 0) (h₂ : ∀ f, Q (0, f) = 0)
    (hQ : ∀ (g : BinaryLinear.GL V) v, Q (naturalDualRepresentation g v) = Q v)
    {v : Space V} (hv : quadratic v = 0) : Q v = 0 := by
  by_cases hx : v.1 = 0
  · have he : v = (0, v.2) := Prod.ext hx rfl
    rw [he, h₂]
  obtain ⟨k, hk⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hx
  have hk' : (k + v.2) v.1 = 1 := by simp [hk, show v.2 v.1 = 0 from hv]
  obtain ⟨g, hg⟩ := exists_naturalDual_eq_of_pairing_one
    (show quadratic (v.1, k) = 1 from hk)
    (show quadratic (v.1, k + v.2) = 1 from hk')
  have he := hQ g (v.1, k)
  rw [hg, quadratic_cross_add Q h₁ h₂] at he
  exact add_left_cancel (he.trans (add_zero _).symm)

/-- The evaluation form is the only nondegenerate inner-invariant form vanishing on both summands. -/
theorem quadratic_unique [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) (Space V))
    (h₁ : ∀ x, Q (x, 0) = 0) (h₂ : ∀ f, Q (0, f) = 0)
    (hQ : ∀ (g : BinaryLinear.GL V) v, Q (naturalDualRepresentation g v) = Q v)
    (hnd : Q.polarBilin.Nondegenerate) : Q = quadratic := by
  ext v
  by_cases hv : quadratic v = 0
  · exact (quadratic_zero_of_pairing_zero Q h₁ h₂ hQ hv).trans hv.symm
  have hv1 := binary_one hv
  have hQv : Q v ≠ 0 := by
    intro hz
    have hall : ∀ w, Q w = 0 := by
      intro w
      by_cases hw : quadratic w = 0
      · exact quadratic_zero_of_pairing_zero Q h₁ h₂ hQ hw
      · obtain ⟨g, hg⟩ := exists_naturalDual_eq_of_pairing_one hv1 (binary_one hw)
        rw [← hg, hQ, hz]
    have he : v = 0 := hnd.1 v (by
      intro w
      simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hall])
    simp [he] at hv
  exact (binary_one hQv).trans hv1.symm

/-- Nonzero vectors in either marked summand. -/
def IsPure (v : Space V) : Prop :=
  (v.1 ≠ 0 ∧ v.2 = 0) ∨ (v.1 = 0 ∧ v.2 ≠ 0)

/-- Both components nonzero, with zero evaluation pairing. -/
def IsSingularDiagonal (v : Space V) : Prop :=
  v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ quadratic v = 0

variable {n : ℕ}

/-- Full automorphism invariance follows from the inner/graph description. -/
theorem coordinate_quadratic_invariant (hn : n = 4 ∨ n = 5)
    (A : CoordinateAction n) (a : MulAut (BinaryLinear.OuterCyclic.LinearGroup n))
    (v : CoordinateSpace n) : quadratic (A.representation a v) = quadratic v := by
  obtain ⟨g, rfl | rfl⟩ := BinaryLinear.OuterCyclic.inner_graph hn a
  · rw [A.on_inner]
    rw [naturalDualRepresentation_apply]
    exact quadratic_invariant g v
  · rw [map_mul]
    change quadratic (A.representation (BinaryLinear.OuterCyclic.graphLinear n)
      (A.representation (MulAut.conj g) v)) = quadratic v
    rw [A.on_inner, A.on_graph, coordinateSwap_quadratic]
    rw [naturalDualRepresentation_apply]
    exact quadratic_invariant g v

/-- The full action preserves the union of the two punctured marked summands. -/
theorem coordinate_isPure_iff (hn : n = 4 ∨ n = 5) (A : CoordinateAction n)
    (a : MulAut (BinaryLinear.OuterCyclic.LinearGroup n)) (v : CoordinateSpace n) :
    IsPure (A.representation a v) ↔ IsPure v := by
  have hi (g : BinaryLinear.OuterCyclic.LinearGroup n) (w : CoordinateSpace n) :
      IsPure (naturalDualRepresentation g w) ↔ IsPure w := by
    simp [IsPure, naturalDualRepresentation_apply]
  have hs (w : CoordinateSpace n) : IsPure (coordinateSwap n w) ↔ IsPure w := by
    simp only [IsPure, coordinateSwap_apply, LinearEquiv.map_eq_zero_iff, ne_eq]
    tauto
  obtain ⟨g, rfl | rfl⟩ := BinaryLinear.OuterCyclic.inner_graph hn a
  · rw [A.on_inner]; exact hi g v
  · rw [map_mul]
    change IsPure (A.representation (BinaryLinear.OuterCyclic.graphLinear n)
      (A.representation (MulAut.conj g) v)) ↔ IsPure v
    rw [A.on_inner, A.on_graph, hs, hi]

/-- The swap forces the second marked summand to be totally singular too. -/
theorem coordinate_quadratic_unique (A : CoordinateAction n)
    (Q : QuadraticForm (ZMod 2) (CoordinateSpace n))
    (h₁ : ∀ x, Q (x, 0) = 0)
    (hQ : ∀ a v, Q (A.representation a v) = Q v)
    (hnd : Q.polarBilin.Nondegenerate) : Q = quadratic := by
  apply quadratic_unique Q h₁
  · intro f
    have he := hQ (BinaryLinear.OuterCyclic.graphLinear n)
      ((dotProductEquiv (ZMod 2) (Fin n)).symm f, 0)
    rw [A.on_graph, coordinateSwap_apply] at he
    simpa only [map_zero, LinearEquiv.apply_symm_apply, h₁] using he
  · intro g v
    rw [← A.on_inner]
    exact hQ _ _
  · exact hnd

private theorem exists_pure_to_natural (A : CoordinateAction n)
    {v : CoordinateSpace n} (hv : IsPure v)
    {x : BinaryLinear.OuterCyclic.Space n} (hx : x ≠ 0) :
    ∃ a, A.representation a v = (x, 0) := by
  rcases hv with ⟨hv, hv'⟩ | ⟨hv, hv'⟩
  · obtain ⟨g, hg⟩ := BinaryLinear.OuterCyclic.exists_linearEquiv_apply_eq hv hx
    exact ⟨MulAut.conj g, by simp [A.on_inner, naturalDualRepresentation_apply, hv', hg]⟩
  · have hne : (dotProductEquiv (ZMod 2) (Fin n)).symm v.2 ≠ 0 := by simpa using hv'
    obtain ⟨g, hg⟩ := BinaryLinear.OuterCyclic.exists_linearEquiv_apply_eq hne hx
    refine ⟨MulAut.conj g * BinaryLinear.OuterCyclic.graphLinear n, ?_⟩
    rw [map_mul]
    change A.representation (MulAut.conj g)
      (A.representation (BinaryLinear.OuterCyclic.graphLinear n) v) = (x, 0)
    simp [A.on_inner, A.on_graph, coordinateSwap_apply, naturalDualRepresentation_apply, hv, hg]

/-- The full automorphism group is transitive on the pure nonzero vectors. -/
theorem exists_coordinate_eq_of_isPure (hn : 0 < n) (A : CoordinateAction n)
    {v w : CoordinateSpace n} (hv : IsPure v) (hw : IsPure w) :
    ∃ a, A.representation a v = w := by
  let x : BinaryLinear.OuterCyclic.Space n := fun _ => 1
  have hx : x ≠ 0 := by
    intro he
    have hi := congrFun he ⟨0, hn⟩
    exact one_ne_zero hi
  obtain ⟨a, ha⟩ := exists_pure_to_natural A hv hx
  obtain ⟨b, hb⟩ := exists_pure_to_natural A hw hx
  refine ⟨b⁻¹ * a, ?_⟩
  rw [map_mul]
  change A.representation b⁻¹ (A.representation a v) = w
  rw [ha, ← hb]
  change (A.representation b⁻¹ * A.representation b) w = w
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

/-- Inner transitivity on the nonsingular orbit, stated for the actual automorphism action. -/
theorem exists_inner_eq_of_pairing_one (A : CoordinateAction n)
    {v w : CoordinateSpace n} (hv : quadratic v = 1) (hw : quadratic w = 1) :
    ∃ g : BinaryLinear.OuterCyclic.LinearGroup n,
      A.representation (MulAut.conj g) v = w := by
  obtain ⟨g, hg⟩ := exists_naturalDual_eq_of_pairing_one hv hw
  exact ⟨g, (A.on_inner g v).trans hg⟩

/-- Inner transitivity on the singular diagonal orbit. -/
theorem exists_inner_eq_of_singularDiagonal (A : CoordinateAction n)
    {v w : CoordinateSpace n} (hv : IsSingularDiagonal v) (hw : IsSingularDiagonal w) :
    ∃ g : BinaryLinear.OuterCyclic.LinearGroup n,
      A.representation (MulAut.conj g) v = w := by
  obtain ⟨g, hg⟩ := exists_naturalDual_eq hv.1 hw.1 hv.2.1 hw.2.1
    (hv.2.2.trans hw.2.2.symm)
  exact ⟨g, (A.on_inner g v).trans hg⟩

private theorem components_ne_zero_of_not_pure {v : Space V}
    (hv : v ≠ 0) (hp : ¬ IsPure v) : v.1 ≠ 0 ∧ v.2 ≠ 0 := by
  constructor
  · intro hx
    apply hp
    exact Or.inr ⟨hx, fun hf => hv (Prod.ext hx hf)⟩
  · intro hf
    apply hp
    exact Or.inl ⟨fun hx => hv (Prod.ext hx hf), hf⟩

/-- Exact orbit classification on nonzero vectors for the specified actual action. -/
theorem coordinate_orbit_iff (hn : n = 4 ∨ n = 5) (A : CoordinateAction n)
    {v w : CoordinateSpace n} (hv : v ≠ 0) (hw : w ≠ 0) :
    (∃ a, A.representation a v = w) ↔
      (IsPure v ∧ IsPure w) ∨
      (IsSingularDiagonal v ∧ IsSingularDiagonal w) ∨
      (quadratic v = 1 ∧ quadratic w = 1) := by
  constructor
  · rintro ⟨a, ha⟩
    have hp : IsPure v ↔ IsPure w := by
      rw [← ha]
      exact (coordinate_isPure_iff hn A a v).symm
    have hq : quadratic v = quadratic w := by
      rw [← ha, coordinate_quadratic_invariant hn A]
    by_cases hvp : IsPure v
    · exact Or.inl ⟨hvp, hp.mp hvp⟩
    by_cases hvq : quadratic v = 0
    · have hwq : quadratic w = 0 := hq.symm.trans hvq
      exact Or.inr (Or.inl
        ⟨⟨(components_ne_zero_of_not_pure hv hvp).1,
           (components_ne_zero_of_not_pure hv hvp).2, hvq⟩,
         ⟨(components_ne_zero_of_not_pure hw (mt hp.mpr hvp)).1,
           (components_ne_zero_of_not_pure hw (mt hp.mpr hvp)).2, hwq⟩⟩)
    · exact Or.inr (Or.inr ⟨binary_one hvq, hq.symm.trans (binary_one hvq)⟩)
  · rintro (⟨hvp, hwp⟩ | ⟨hvs, hws⟩ | ⟨hvq, hwq⟩)
    · exact exists_coordinate_eq_of_isPure (by omega) A hvp hwp
    · obtain ⟨g, hg⟩ := exists_inner_eq_of_singularDiagonal A hvs hws
      exact ⟨MulAut.conj g, hg⟩
    · obtain ⟨g, hg⟩ := exists_inner_eq_of_pairing_one A hvq hwq
      exact ⟨MulAut.conj g, hg⟩

/-- Each of the three orbit descriptions is inhabited. -/
theorem coordinate_orbit_classes_nonempty (hn : 2 ≤ n) :
    (∃ v : CoordinateSpace n, IsPure v) ∧
    (∃ v : CoordinateSpace n, IsSingularDiagonal v) ∧
    (∃ v : CoordinateSpace n, quadratic v = 1) := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  let x : BinaryLinear.OuterCyclic.Space n := Pi.single i 1
  have hx : x ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp [x] at hi
  have hf : (LinearMap.proj j : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) ≠ 0 := by
    intro h
    have he := LinearMap.congr_fun h (fun _ => 1)
    exact one_ne_zero he
  refine ⟨⟨(x, 0), Or.inl ⟨hx, rfl⟩⟩,
    ⟨(x, LinearMap.proj j), hx, hf, ?_⟩, ⟨(x, LinearMap.proj i), ?_⟩⟩
  · simp [quadratic_apply, x, hij]
  · simp [quadratic_apply, x]

/-- H.9.1(1) on the coordinate model, with the existence of its action still explicit. -/
theorem coordinate_existsUnique_quadratic (hn : n = 4 ∨ n = 5) (A : CoordinateAction n) :
    ∃! Q : QuadraticForm (ZMod 2) (CoordinateSpace n),
      Q.polarBilin.Nondegenerate ∧ (∀ x, Q (x, 0) = 0) ∧
      (∀ a v, Q (A.representation a v) = Q v) := by
  refine ⟨quadratic, ⟨polar_nondegenerate, quadratic_natural,
    coordinate_quadratic_invariant hn A⟩, ?_⟩
  intro Q hQ
  exact coordinate_quadratic_unique A Q hQ.2.1 hQ.2.2 hQ.1

/-- The punctured pure vectors are singular. -/
theorem quadratic_eq_zero_of_isPure {v : Space V} (hv : IsPure v) : quadratic v = 0 := by
  rcases hv with ⟨_, h⟩ | ⟨h, _⟩ <;> simp [quadratic_apply, h]

/-- The three displayed orbit classes are pairwise disjoint. -/
theorem orbit_classes_disjoint (v : Space V) :
    (IsPure v → ¬ IsSingularDiagonal v) ∧
    (IsPure v → quadratic v ≠ 1) ∧
    (IsSingularDiagonal v → quadratic v ≠ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hp hs
    rcases hp with ⟨_, h⟩ | ⟨h, _⟩
    · exact hs.2.1 h
    · exact hs.1 h
  · intro hp
    rw [quadratic_eq_zero_of_isPure hp]
    exact zero_ne_one
  · intro hs
    rw [hs.2.2]
    exact zero_ne_one

/-- Inner and graph values determine the extension uniquely. -/
theorem coordinateAction_representation_unique (hn : n = 4 ∨ n = 5)
    (A B : CoordinateAction n) : A.representation = B.representation := by
  apply MonoidHom.ext
  intro a
  apply LinearMap.ext
  intro v
  obtain ⟨g, rfl | rfl⟩ := BinaryLinear.OuterCyclic.inner_graph hn a
  · rw [A.on_inner, B.on_inner]
  · simp only [map_mul, Module.End.mul_apply, A.on_inner, B.on_inner, A.on_graph, B.on_graph]
end BinaryNaturalDual.ModelOrbits
