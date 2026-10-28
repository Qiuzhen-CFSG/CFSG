module

public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.MaximalCover.Geometry
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# The basis-line case in PSU₄(3)

For any basis whose lines are permuted by the full SU preimage, uniqueness
of the target line constructs a homomorphism to S₄. Its kernel acts diagonally
in that basis, so its elements commute. Extending permutations to seven letters
therefore gives one of the concrete kernel models. The whole preimage is also
solvable, since S₄ is solvable.

No orthogonality of the basis is required. This closes the monomial case of
the irreducible proper-section obligation in Aschbacher–Smith, Theorem 0.1.2(4),
condition K, printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

public noncomputable section
namespace CFSG.Quasithin.MainConverse.UnitaryFourIrreducible

open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

private theorem basis_smul_index
    (b : Module.Basis (Fin 4) FiniteField.Nine (Fin 4 → FiniteField.Nine))
    {i j : Fin 4} {a c : FiniteField.Nine} (ha : a ≠ 0)
    (h : a • b i = c • b j) : i = j := by
  by_contra hij
  have hc := congrArg (fun v => b.repr v i) h
  exact ha (by simpa [hij, Ne.symm hij] using hc)

/-- The actual action on four basis lines has abelian kernel. -/
theorem IsMonomial.exists_permutation_hom (U : Subgroup (Carrier 4))
    (h : IsMonomial U) :
    ∃ f : fullPreimage U →* Equiv.Perm (Fin 4), IsMulCommutative f.ker := by
  classical
  obtain ⟨b, hb⟩ := h
  let σ (g : fullPreimage U) : Equiv.Perm (Fin 4) := (hb g).choose
  have hσ (g : fullPreimage U) (i : Fin 4) :
      ∃ a : FiniteField.Nine, a ≠ 0 ∧ liftedRepresentation U g (b i) = a • b (σ g i) :=
    (hb g).choose_spec i
  let f : fullPreimage U →* Equiv.Perm (Fin 4) :=
    { toFun := σ
      map_one' := by
        apply Equiv.ext
        intro i
        obtain ⟨a, ha, he⟩ := hσ 1 i
        apply (basis_smul_index b one_ne_zero (a := 1) (c := a) ?_).symm
        simpa using he
      map_mul' := by
        intro g k
        apply Equiv.ext
        intro i
        obtain ⟨c, hc, he⟩ := hσ (g * k) i
        obtain ⟨a, _, hg⟩ := hσ g (σ k i)
        obtain ⟨d, _, hk⟩ := hσ k i
        apply basis_smul_index b hc (c := d * a)
        rw [← he, map_mul, Module.End.mul_apply, hk, map_smul, hg, smul_smul]
        rfl }
  refine ⟨f, ⟨⟨?_⟩⟩⟩
  intro x y
  apply Subtype.ext
  apply liftedRepresentation_injective U
  apply b.ext
  intro i
  obtain ⟨a, _, hx⟩ := hσ x.val i
  obtain ⟨c, _, hy⟩ := hσ y.val i
  have hxi : liftedRepresentation U x.val (b i) = a • b i := by
    simpa only [show σ x.val = 1 from x.property, Equiv.Perm.one_apply] using hx
  have hyi : liftedRepresentation U y.val (b i) = c • b i := by
    simpa only [show σ y.val = 1 from y.property, Equiv.Perm.one_apply] using hy
  change liftedRepresentation U (x.val * y.val) (b i) =
    liftedRepresentation U (y.val * x.val) (b i)
  simp only [map_mul, Module.End.mul_apply, hxi, hyi, map_smul, smul_smul, mul_comm]

/-- Extending the four-letter action supplies the required concrete S₇ map. -/
theorem IsMonomial.hasSolvableKernelModel (U : Subgroup (Carrier 4))
    (h : IsMonomial U) : HasSolvableKernelModel (fullPreimage U) := by
  obtain ⟨f, hf⟩ := h.exists_permutation_hom U
  let := hf
  let e := Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (show 4 ≤ 7 by decide))
  refine Or.inl ⟨e.comp f, ?_⟩
  rw [MonoidHom.ker_comp_of_injective f e (Equiv.Perm.viaEmbeddingHom_injective _)]
  exact Group.isSolvable_of_comm fun _ _ => IsMulCommutative.is_comm.comm _ _

/-- In fact every such full preimage is solvable. -/
theorem IsMonomial.fullPreimage_isSolvable (U : Subgroup (Carrier 4))
    (h : IsMonomial U) : Group.IsSolvable (fullPreimage U) := by
  obtain ⟨f, hf⟩ := h.exists_permutation_hom U
  let := hf
  let : Group.IsSolvable f.ker :=
    Group.isSolvable_of_comm fun _ _ => IsMulCommutative.is_comm.comm _ _
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by simp)

end CFSG.Quasithin.MainConverse.UnitaryFourIrreducible
