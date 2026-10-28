module

public import Theory.AlgebraicGroup.Instance.GL
public import Theory.AlgebraicGroup.Variety.Zariski

universe u v

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

public def stabMatrixSet (n r : ℕ) : Set (Variety.Point (glVariety n : Variety k)) :=
  {x | ∀ i j : Fin n, r ≤ i.1 → j.1 < r → glMatrixOfPoint n x i j = 0}

omit [IsAlgClosed k] in
/-- `stabMatrixSet` is Zariski closed, since its lower-left entries are polynomial equations. -/
public lemma stabMatrixSet_closed (n r : ℕ) :
    IsZariskiClosed (glVariety n : Variety k) (stabMatrixSet n r) := by
  refine ⟨{p | ∃ i j : Fin n, r ≤ i.1 ∧ j.1 < r ∧ p = MvPolynomial.X (Sum.inl (i, j))}, ?_⟩
  ext x
  constructor
  · intro hx p hp
    rcases hp with ⟨i, j, hij₁, hij₂, rfl⟩
    rw [evalPolynomial_X]
    exact hx i j hij₁ hij₂
  · intro hx i j hij₁ hij₂
    have he := hx (MvPolynomial.X (Sum.inl (i, j))) ⟨i, j, hij₁, hij₂, rfl⟩
    simpa [glMatrixOfPoint, evalPolynomial] using he

/-- The subgroup of `GL(V)` preserving a subspace `W`. -/
@[expose]
public def subspaceStabilizer (k : Type u) [Field k] [IsAlgClosed k]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (W : Submodule k V) : Subgroup (LinearMap.GeneralLinearGroup k V) where
  carrier := {g : LinearMap.GeneralLinearGroup k V |
    ∀ w : V, w ∈ W → (g : V →ₗ[k] V) w ∈ W}
  one_mem' := by
    intro w hw
    simpa using hw
  mul_mem' := by
    intro a b ha hb w hw
    exact ha _ (hb _ hw)
  inv_mem' := by
    intro a ha w hw
    let e := LinearMap.GeneralLinearGroup.toLinearEquiv a
    have hmap : ∀ x : W, e x.1 ∈ W := fun x => ha x.1 x.2
    let f : W →ₗ[k] W := (e.toLinearMap.comp W.subtype).codRestrict W (fun x => hmap x)
    have hf_inj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact e.injective (by
        change (f x).1 = (f y).1
        exact congrArg Subtype.val hxy)
    have hf_surj : Function.Surjective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := k) (V := W) (V₂ := W) rfl).mp hf_inj
    rcases hf_surj ⟨w, hw⟩ with ⟨x, hx⟩
    have hew : e x.1 = w := congrArg Subtype.val hx
    have hxw : e.symm w = x.1 := by
      calc
        e.symm w = e.symm (e x.1) := by rw [hew]
        _ = x.1 := e.symm_apply_apply x.1
    have haInv : ((a⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) w = x.1 := by
      calc
        ((a⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) w = e.symm w := by
          have h1 : LinearMap.GeneralLinearGroup.toLinearEquiv (a⁻¹) = e.symm := by
            rw [LinearMap.GeneralLinearGroup.toLinearEquiv_inv]
            change (e)⁻¹ = e.symm
            rfl
          have h2 : (LinearMap.GeneralLinearGroup.toLinearEquiv (a⁻¹)).toLinearMap =
              ((a⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) := by
            rfl
          rw [← h2, h1]
          rfl
        _ = x.1 := hxw
    rw [haInv]
    exact x.2

omit [IsAlgClosed k] in
/-- A basis vector `e i` with `i ≥ r` is outside the span of the first `r`
basis vectors; coordinates of a span element vanish beyond the first `r`. -/
public lemma basisSpanCoord (V : Type v) [AddCommGroup V] [Module k V]
    (n : ℕ) (e : Module.Basis (Fin n) k V) (r : ℕ) (hr : r ≤ n)
    (v : Fin n → k) :
    e.equivFun.symm v ∈ Submodule.span k (Set.range (fun j : Fin r => e (Fin.castLE hr j))) ↔
      ∀ i : Fin n, r ≤ i.1 → v i = 0 := by
  constructor
  · intro h i hi
    let p : Submodule k V :=
      { carrier := {x : V | ∀ i : Fin n, r ≤ i.1 → e.repr x i = 0}
        zero_mem' := by intro i hi; simp
        add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi]
        smul_mem' := by intro c x hx i hi; simp [hx i hi] }
    have hgen : ∀ x ∈ Set.range (fun j : Fin r => e (Fin.castLE hr j)), x ∈ p := by
      intro x hx
      rcases hx with ⟨j, rfl⟩
      change ∀ i : Fin n, r ≤ i.1 → e.repr (e (Fin.castLE hr j)) i = 0
      intro i hi
      rw [Module.Basis.repr_self]
      by_cases hji : (Fin.castLE hr j) = i
      · exfalso
        have hj : (Fin.castLE hr j).1 < r := j.2
        have hle : r ≤ i.1 := hi
        have hlt : (Fin.castLE hr j).1 < i.1 := lt_of_lt_of_le hj hle
        have heq : (Fin.castLE hr j).1 = i.1 := congrArg Fin.val hji
        exact (ne_of_lt hlt) heq
      · simp [hji]
    have hspan : Submodule.span k (Set.range (fun j : Fin r => e (Fin.castLE hr j))) ≤ p :=
      Submodule.span_le.mpr hgen
    have hw : e.equivFun.symm v ∈ p := hspan h
    have hwcoord : e.repr (e.equivFun.symm v) = v := by
      have hsymm : e.equivFun.symm v = ∑ i, v i • e i := Module.Basis.equivFun_symm_apply e v
      rw [hsymm]
      ext i
      simp [Module.Basis.repr_self]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b hb hbi
        simp [hbi]
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ i))
    have hvi : e.repr (e.equivFun.symm v) i = 0 := hw i hi
    rw [hwcoord] at hvi
    exact hvi
  · intro h
    rw [Module.Basis.equivFun_symm_apply]
    have hstep : (∑ i : Fin n, v i • e i) =
        ∑ j : Fin r, v (Fin.castLE hr j) • e (Fin.castLE hr j) := by
      let s : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.1 < r)
      have h1 : (∑ i : Fin n, v i • e i) = ∑ i ∈ s, v i • e i := by
        symm
        refine Finset.sum_subset ?_ ?_
        · intro i hi
          exact Finset.mem_univ i
        · intro i hi hin
          have hge : r ≤ i.1 := by
            apply le_of_not_gt
            intro hlt
            exact hin (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩)
          have hvi : v i = 0 := h i hge
          simp [hvi]
      have h2 : (∑ i ∈ s, v i • e i) = ∑ j : Fin r, v (Fin.castLE hr j) • e (Fin.castLE hr j) := by
        refine Finset.sum_bij (fun i hi => ⟨i.1, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_ ?_
        · intro i hi
          exact Finset.mem_univ _
        · intro a ha b hb h
          apply Fin.ext
          simpa using congrArg Fin.val h
        · intro j hj
          refine ⟨Fin.castLE hr j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩, ?_⟩
          apply Fin.ext
          rfl
        · intro i hi
          have hcast : Fin.castLE hr ⟨i.1, (Finset.mem_filter.mp hi).2⟩ = i := by
            apply Fin.ext
            rfl
          rw [hcast]
      rw [h1, h2]
    rw [hstep]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨j, rfl⟩

/-- The basis matrix of a point preserves `W` (spanned by the first `r` basis
vectors) exactly when its lower-left block is zero. -/
public lemma subspaceStabilizer_matrix_iff (V : Type v) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (W : Submodule k V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (r : ℕ) (hr : r ≤ Module.finrank k V)
    (hW : W = Submodule.span k (Set.range (fun j : Fin r => e (Fin.castLE hr j)))) :
    ∀ x : Variety.Point (glVarietyOf k V),
      x ∈ stabMatrixSet (Module.finrank k V) r ↔
        (glPointEquivOf k V e) x ∈ subspaceStabilizer k V W := by
  intro x
  constructor
  · intro hx w hw
    rw [hW] at hw
    let S : Set V := Set.range (fun j : Fin r => e (Fin.castLE hr j))
    have hgen : ∀ y ∈ S, (glPointEquivOf k V e x).1 y ∈ Submodule.span k S := by
      intro y hy
      rcases hy with ⟨j, rfl⟩
      -- The image of `e (castLE j)` is the inverse coordinate map applied to
      -- the corresponding column, hence lies in `span S`.
      rw [glPointEquivOf_apply_basis]
      apply (basisSpanCoord V (Module.finrank k V) e r hr (fun l : Fin (Module.finrank k V) =>
        glMatrixOfPoint (Module.finrank k V) x l (Fin.castLE hr j))).mpr
      intro i hi
      exact hx i (Fin.castLE hr j) hi j.2
    let p : Submodule k V :=
      { carrier := {y : V | (glPointEquivOf k V e x).1 y ∈ Submodule.span k S}
        zero_mem' := by simp
        add_mem' := by
          intro y z hy hz
          change (glPointEquivOf k V e x).1 (y + z) ∈ Submodule.span k S
          rw [map_add]
          exact Submodule.add_mem (Submodule.span k S) hy hz
        smul_mem' := by
          intro c y hy
          change (glPointEquivOf k V e x).1 (c • y) ∈ Submodule.span k S
          rw [map_smul]
          exact Submodule.smul_mem (Submodule.span k S) c hy }
    have hspan_le : Submodule.span k S ≤ p := Submodule.span_le.mpr hgen
    simpa [p, hW] using hspan_le hw
  · intro hg i j hij₁ hij₂
    have hej : e j ∈ W := by
      rw [hW]
      exact Submodule.subset_span ⟨⟨j.1, hij₂⟩, by
        apply congrArg e
        apply Fin.ext
        rfl⟩
    have hgj : (glPointEquivOf k V e x).1 (e j) ∈ W := hg (e j) hej
    rw [glPointEquivOf_apply_basis] at hgj
    rw [hW] at hgj
    have hcol := (basisSpanCoord V (Module.finrank k V) e r hr (fun l : Fin (Module.finrank k V) =>
      glMatrixOfPoint (Module.finrank k V) x l j)).mp hgj
    exact hcol i hij₁

end

end Theory.AlgebraicGroup

