module

public import Theory.AlgebraicGroup.Bor1.DerivationSingleRowMinor
public import Theory.AlgebraicGroup.Bor1.RepresentationDifferential

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped BigOperators

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- A linear matrix coefficient between basis vectors is the corresponding
ordinary matrix coefficient. -/
public lemma rationalRepresentationLinearMatrixCoefficient_basis
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (i j : Fin (Module.finrank k V)) :
    rationalRepresentationLinearMatrixCoefficient ρ e f (e.coord i) (e j) =
      rationalRepresentationMatrixCoefficient ρ e f i j := by
  classical
  rw [rationalRepresentationLinearMatrixCoefficient]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]
  simp only [apply_ite]
  simp

/-- A single-row exterior minor reads one matrix coordinate of the original
infinitesimal representation. -/
public theorem rationalRepresentationDifferential_singleRowMinor
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g)
    (D : IdentityPointDerivation G) {n : ℕ}
    (c : Fin n ↪ Fin (Module.finrank k V)) (i₀ : Fin n)
    (a : Fin (Module.finrank k V)) (ha : a ∉ Set.range c) :
    D (Matrix.det fun i j : Fin n =>
      rationalRepresentationMatrixCoefficient ρ e f
        (Function.update (fun x => c x) i₀ a i) (c j)) =
      e.coord a (rationalRepresentationDifferential ρ e f D (e (c i₀))) := by
  let M : Matrix (Fin (Module.finrank k V))
      (Fin (Module.finrank k V)) G.PolynomialFunction :=
    fun i j => rationalRepresentationMatrixCoefficient ρ e f i j
  have hM : ∀ i j, M i j 1 = if i = j then 1 else 0 := by
    intro i j
    rw [rationalRepresentationMatrixCoefficient_apply ρ e f hf]
    rw [show ρ.action 1 = 1 by exact map_one ρ.action]
    change e.repr (e j) i = _
    rw [Module.Basis.repr_self]
    by_cases hij : i = j
    · subst i
      simp
    · rw [Finsupp.single_eq_of_ne]
      · simp [hij]
      · exact hij
  have hminor := identityPointDerivation_det_singleRowReplacement
    D c i₀ a ha M hM
  change D (Matrix.det fun i j : Fin n =>
      M (Function.update (fun x => c x) i₀ a i) (c j)) = _
  rw [hminor]
  rw [rationalRepresentationDifferential_linearMatrixCoefficient]
  rw [rationalRepresentationLinearMatrixCoefficient_basis]

end Theory.AlgebraicGroup.Bor1
