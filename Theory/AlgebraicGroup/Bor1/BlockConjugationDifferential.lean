module

public import Theory.AlgebraicGroup.Bor1.ConjugationDifferential
public import Theory.AlgebraicGroup.Bor1.RepresentationDifferentialIntertwining

universe u v w

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- A zero differential for the block-conjugation representation forces the
original representation differential to centralize every block-diagonal
endomorphism. -/
public theorem blockDiagonalEnd_rationalRepresentationDifferential_eq_zero_imp_centralizes
    {ι : Type w} (E : ι → Submodule k V)
    (ρ : RationalRepresentation G V)
    (σ : Variety.Point G →* Equiv.Perm ι)
    (hE : ∀ g i, Submodule.map
      ((ρ.action g : LinearMap.GeneralLinearGroup k V) : Module.End k V) (E i) =
        E ((σ g : Equiv ι ι) i))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V b (f.onPoints g) = ρ.action g)
    (e : Module.Basis (Fin (Module.finrank k (blockDiagonalEnd E))) k
      (blockDiagonalEnd E))
    (q : AlgebraicGroup.Morphism G (glVarietyOf k (blockDiagonalEnd E)))
    (hq : ∀ g, glPointEquivOf k (blockDiagonalEnd E) e (q.onPoints g) =
      (blockDiagonalEndConjRationalRepresentation E ρ σ hE).action g)
    (D : IdentityPointDerivation G)
    (hzero : rationalRepresentationDifferential
      (blockDiagonalEndConjRationalRepresentation E ρ σ hE) e q D = 0) :
    ∀ u : blockDiagonalEnd E,
      Commute (rationalRepresentationDifferential ρ b f D) u.1 := by
  have hρrat : IsRationalRepresentation ρ := ⟨b, f, hf⟩
  obtain ⟨c, F, hF⟩ := conjEndRationalRepresentation_isRational ρ hρrat
  have hinter : Intertwines
      (blockDiagonalEndConjRationalRepresentation E ρ σ hE)
      (conjEndRationalRepresentation ρ) (blockDiagonalEnd E).subtype := by
    intro g u
    change ((blockDiagonalEnd_conjLinearMap E (σ g) (ρ.action g)
        (hE g) u : blockDiagonalEnd E) : Module.End k V) =
      conjEndLinearMap (ρ.action g) u.1
    exact blockDiagonalEnd_conjLinearMap_apply E (σ g) (ρ.action g) (hE g) u
  intro u
  have hdiff := rationalRepresentationDifferential_intertwines
    (blockDiagonalEndConjRationalRepresentation E ρ σ hE)
    (conjEndRationalRepresentation ρ) (blockDiagonalEnd E).subtype hinter
    e q hq c F hF D u
  rw [hzero] at hdiff
  have hconjzero :
      rationalRepresentationDifferential
        (conjEndRationalRepresentation ρ) c F D u.1 = 0 := by
    simpa using hdiff.symm
  rw [rationalRepresentationDifferential_conjEnd_apply
    ρ b f hf c F hF D] at hconjzero
  change rationalRepresentationDifferential ρ b f D * u.1 -
    u.1 * rationalRepresentationDifferential ρ b f D = 0 at hconjzero
  rw [sub_eq_zero] at hconjzero
  exact (commute_iff_eq _ _).mpr hconjzero

end Theory.AlgebraicGroup.Bor1
