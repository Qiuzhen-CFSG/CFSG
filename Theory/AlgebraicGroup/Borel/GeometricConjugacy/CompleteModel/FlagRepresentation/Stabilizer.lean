module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagData
public import Theory.AlgebraicGroup.Representations.Unipotent.Flag
public import Theory.AlgebraicGroup.Instance.U

/-! A faithful full-flag stabilizer is solvable: use a basis adapted to the flag
to embed it in the triangular group, whose diagonal kernel is unitriangular.
This is the second linear assertion in Borel, *Linear Algebraic Groups*, §11.1. -/

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy

universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem diagonal_val (n : ℕ) (A : tTriangularGL k n) (i : Fin n) :
    (↑(tDiagonalHom n A i) : k) = A.1.1 i i := by
  let x := (tPointEquiv k n).symm A
  simpa only [x, Equiv.apply_symm_apply, tPointMatrix,
    tPointEquiv_symm_val_inl] using tDiagonalHom_val n x i

/-- Upper-triangular invertible matrices form a solvable group. -/
public theorem triangularGroup_isSolvable (n : ℕ) :
    Group.IsSolvable (tTriangularGL k n) := by
  let U := uUnipotentGL k n
  let f : U →* (tDiagonalHom (k := k) n).ker :=
    { toFun := fun A => ⟨uToTHom n A, by
        ext i
        rw [diagonal_val]
        change A.1.1 i i = 1
        exact A.2.2 i⟩
      map_one' := by apply Subtype.ext; exact map_one (uToTHom (k := k) n)
      map_mul' := by intro A B; apply Subtype.ext; exact map_mul (uToTHom (k := k) n) A B }
  have hf : Function.Surjective f := by
    intro A
    have hdiag : ∀ i : Fin n, A.1.1.1 i i = 1 := by
      intro i
      have hi := congrArg (fun z : kˣ => (z : k)) (congrFun A.2 i)
      rw [diagonal_val] at hi
      exact hi
    exact ⟨⟨A.1.1, A.1.2, hdiag⟩, rfl⟩
  let : Group.IsNilpotent U := uUnipotentGL_isNilpotent n
  let : Group.IsSolvable (tDiagonalHom (k := k) n).ker :=
    Group.isSolvable_of_surjective hf
  let : Group.IsSolvable (Fin n → kˣ) :=
    Group.isSolvable_of_comm fun _ _ => mul_comm _ _
  exact Group.isSolvable_of_ker_le_range
    (tDiagonalHom (k := k) n).ker.subtype (tDiagonalHom n)
    (fun A hA => ⟨⟨A, hA⟩, rfl⟩)

/-- The abstract subgroup stabilizing a full flag in a faithful representation. -/
public abbrev flagStabilizer {G : Variety k} [AlgebraicGroup G]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation G V) (F : FullFlag k V) : Subgroup (Variety.Point G) :=
  @MulAction.stabilizer (Variety.Point G) (FullFlag k V) _ (flagAction ρ) F

/-- Every stabilizer of a full flag in a faithful finite-dimensional representation
is solvable. Rationality and connectedness are unnecessary for this assertion. -/
public theorem flagStabilizer_isSolvable {G : Variety k} [AlgebraicGroup G]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation G V) (hρ : Function.Injective ρ.action)
    (F : FullFlag k V) : Group.IsSolvable (flagStabilizer ρ F) := by
  let H := flagStabilizer ρ F
  let σ : Representation k H V :=
    (Units.coeHom (Module.End k V)).comp (ρ.action.comp H.subtype)
  obtain ⟨b, hb⟩ := exists_basis_adapted_to_full_submodule_chain
    F.subspace F.monotone F.finrank_eq
  have hstable : ∀ (m : ℕ) (g : H), F.subspace m ≤ (F.subspace m).comap (σ g) := by
    intro m g x hx
    have heq := congrArg (fun F : FullFlag k V => F.subspace m) g.property
    change (F.subspace m).map (ρ.action g.1 : Module.End k V) = F.subspace m at heq
    change (ρ.action g.1 : Module.End k V) x ∈ F.subspace m
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  let toGL := (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp
    (ρ.action.comp H.subtype)
  let toT : H →* tTriangularGL k (Module.finrank k V) :=
    toGL.codRestrict (tTriangularGL k (Module.finrank k V)) (fun g => by
      intro i j hji
      exact Subrepresentation.representation_toMatrix_basis_belowDiagonal_eq_zero
        σ b F.subspace hstable hb g hji)
  have hinj : Function.Injective toT := by
    intro g h heq
    apply Subtype.ext
    apply hρ
    apply (Matrix.GeneralLinearGroup.toLin' b).symm.injective
    exact congrArg (fun A : tTriangularGL k (Module.finrank k V) => A.1) heq
  let : Group.IsSolvable (tTriangularGL k (Module.finrank k V)) :=
    triangularGroup_isSolvable _
  exact Group.isSolvable_of_isSolvable_injective hinj

end Theory.AlgebraicGroup.BorelGeometricConjugacy
