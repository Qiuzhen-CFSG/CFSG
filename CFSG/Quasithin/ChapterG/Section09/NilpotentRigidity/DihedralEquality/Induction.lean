module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.InductionContracts
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.Transport

/-!
# The rank-zero case and assembly of the equality induction

The empty product forces the cubic degree bound to be zero, so its
classification uses an empty internal product and an empty direct sum.
Strong induction then reduces the uniform classification to the positive
step. The final embedding transfer preserves all factor inclusions and
the exceptional first factor.

The positive step is an explicit remaining premise. These reductions do
not assert that the positive-rank cases of Aschbacher--Smith G.9.2 have
been completed. Source: G.9.2, printed pp.351--353.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity

universe u v

namespace DihedralEquality

/-- The degree input applies to the actual subtype-indexed products used
by the equality induction, without assumptions on the cardinality. -/
theorem dihedralDegree_fintype (bounds : DihedralDegreeTheorem.{v})
    {ι : Type u} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (ho : ∀ i, Odd (p i))
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W)
    (hfaith : Function.Injective σ) :
    2 * Fintype.card ι ≤ Module.finrank (ZMod 2) W ∧
      ((∃ i, p i ≠ 3) → 2 * (Fintype.card ι + 1) ≤ Module.finrank (ZMod 2) W) ∧
      ((∃ i, 5 < p i) → 2 * (Fintype.card ι + 1) < Module.finrank (ZMod 2) W) := by
  classical
  let e := (Fintype.equivFin ι).symm
  let f : (∀ i, DihedralGroup (p i)) ≃* ∀ j, DihedralGroup (p (e j)) :=
    { toFun := fun g j => g (e j)
      invFun := Equiv.piCongrLeft (fun i => DihedralGroup (p i)) e
      left_inv := fun g =>
        (Equiv.piCongrLeft (fun i => DihedralGroup (p i)) e).apply_symm_apply g
      right_inv := by intro g; funext j; simp only [Equiv.piCongrLeft_apply_apply]
      map_mul' := fun _ _ => rfl }
  have h := bounds W (Fintype.card ι) (fun j => p (e j))
    (fun j => hp (e j)) (fun j => ho (e j))
    (σ.comp f.symm.toMonoidHom) (hfaith.comp f.symm.injective)
  refine ⟨h.1, ?_, ?_⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    exact h.2.1 ⟨j, hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    exact h.2.2 ⟨j, hi⟩


/-- The empty product has the empty internal decomposition. -/
theorem equalityAt_zero : EqualityAt.{v} 0 := by
  intro ι _ _ hcard p _ _ W _ _ _ σ _
  let : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
  let : Unique (⊤ : Subgroup (∀ i, DihedralGroup (p i))) :=
    ⟨⟨1, Subgroup.mem_top _⟩, fun _ => Subsingleton.elim _ _⟩
  constructor
  · intro _ hdim
    have hd : Module.finrank (ZMod 2) W = 0 := by omega
    let : Subsingleton W := Module.finrank_zero_iff.mp hd
    let dec : InternalDecomposition σ ⊤ 0 :=
      { factor := Fin.elim0
        groupEquiv := MulEquiv.ofUnique
        group_inclusion := fun i => Fin.elim0 i
        spaceEquiv := LinearEquiv.ofSubsingleton _ _
        space_inclusion := fun i => Fin.elim0 i }
    exact ⟨⟨0, dec, False.elim, fun i => Fin.elim0 i⟩⟩
  · rintro ⟨i, _⟩
    exact isEmptyElim i

/-- Strong induction, with the positive-rank construction still explicit. -/
theorem equalityAt_of_positiveStep (step : PositiveEqualityStep.{v}) :
    ∀ r, EqualityAt.{v} r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : r = 0
    · simpa only [hr] using equalityAt_zero.{v}
    · exact step r (Nat.pos_of_ne_zero hr) ih

end DihedralEquality

/-- Transfer a uniform classification of products to their actual embedded
ranges. This theorem does not assert the uniform classification premise. -/
theorem dihedralEqualityCases_of_uniform
    (classify : ∀ r, DihedralEquality.EqualityAt.{v} r)
    {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hfaith : Function.Injective ρ) :
    HasDihedralEqualityCases ρ := by
  intro r D
  have h := classify r (Fin r) (Fintype.card_fin r) D.prime
    D.prime_isPrime D.prime_odd V (ρ.comp D.embedding) (hfaith.comp D.injective)
  constructor
  · intro hp hd
    obtain ⟨d⟩ := h.1 hp hd
    simpa only [← MonoidHom.range_eq_map] using
      Nonempty.intro (d.mapEmbedding ρ D.embedding D.injective)
  · intro hp hd
    obtain ⟨d⟩ := h.2 hp hd
    simpa only [← MonoidHom.range_eq_map] using
      Nonempty.intro (d.mapEmbedding ρ D.embedding D.injective)

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity
