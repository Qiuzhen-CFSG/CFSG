module

public import Theory.Representation.CyclicDefect.ProjectivePairing.IntegralLifting.Contracts

/-!
# Transport and assembly of integral projective lifts

Entrywise coefficient maps preserve intertwining equivalences: apply the map
to both matrices of an equivalence and its inverse. This works for residue
maps as well as embeddings. It makes coefficient reduction and subsequent
extension compatible with the literal `mapCoefficients` representations.

The final construction assembles a complete coefficient ring and an actual
projective residue lift into `IntegralLift`, including the maximal-ideal
kernel and both chosen roots. Existence of these two inputs is a separate
obligation (Feit, *The Representation Theory of Finite Groups*, I.12--13,
I.17, and the lift used in IV.3.3).
-/

public section
noncomputable section
namespace Representation.CyclicDefect.ProjectivePairing.IntegralLifting
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  {G : Type*} [Group G] {n d e : ℕ}

private def coefficientLinear (f : R →+* S)
    (u : (Fin n → R) →ₗ[R] (Fin d → R)) : (Fin n → S) →ₗ[S] (Fin d → S) :=
  Matrix.toLin' ((LinearMap.toMatrix' u).map f)

private theorem coefficientLinear_comp (f : R →+* S)
    (u : (Fin d → R) →ₗ[R] (Fin e → R))
    (v : (Fin n → R) →ₗ[R] (Fin d → R)) :
    coefficientLinear f (u.comp v) = (coefficientLinear f u).comp (coefficientLinear f v) := by
  apply LinearMap.toMatrix'.injective
  simp only [coefficientLinear, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_comp]
  exact Matrix.map_mul

private theorem coefficientLinear_id (f : R →+* S) :
    coefficientLinear f (LinearMap.id : (Fin n → R) →ₗ[R] (Fin n → R)) = LinearMap.id := by
  apply LinearMap.toMatrix'.injective
  simp [coefficientLinear]

private theorem coefficientLinear_rep (f : R →+* S)
    (ρ : Representation R G (Fin n → R)) (g : G) :
    coefficientLinear f (ρ g) = mapCoefficients f ρ g := by
  apply LinearMap.toMatrix'.injective
  rw [mapCoefficients_toMatrix]
  exact LinearMap.toMatrix'_toLin' _

/-- Entrywise coefficient maps preserve an actual intertwining equivalence,
including when the map has a kernel. -/
def coefficientEquiv (f : R →+* S)
    {ρ : Representation R G (Fin n → R)} {σ : Representation R G (Fin d → R)}
    (a : ρ.Equiv σ) : (mapCoefficients f ρ).Equiv (mapCoefficients f σ) := by
  let u := coefficientLinear f a.toLinearMap
  let v := coefficientLinear f a.symm.toLinearMap
  have hvu : v.comp u = LinearMap.id := by
    rw [← coefficientLinear_comp]
    have h : a.symm.toLinearMap.comp a.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact a.symm_apply_apply x
    rw [h, coefficientLinear_id]
  have huv : u.comp v = LinearMap.id := by
    rw [← coefficientLinear_comp]
    have h : a.toLinearMap.comp a.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact a.apply_symm_apply x
    rw [h, coefficientLinear_id]
  refine .mk (LinearEquiv.ofLinearMap u v huv hvu) ?_
  intro g
  change u.comp (mapCoefficients f ρ g) = (mapCoefficients f σ g).comp u
  rw [← coefficientLinear_rep, ← coefficientLinear_rep,
    ← coefficientLinear_comp, ← coefficientLinear_comp]
  exact congrArg (coefficientLinear f) (a.toIntertwiningMap.isIntertwining' g)

/-- Coefficient reduction and subsequent extension compose literally. -/
theorem mapCoefficients_comp (f : R →+* S) (j : S →+* T)
    (ρ : Representation R G (Fin n → R)) :
    mapCoefficients j (mapCoefficients f ρ) = mapCoefficients (j.comp f) ρ := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.toMatrix'.injective
  simp only [mapCoefficients_toMatrix]
  rfl

variable {k K V : Type*} [Field k] [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {m : ℕ}

/-- Assemble the literal residue equivalence with the chosen embedding of the
coefficient field into the final modular field. -/
def assemble {L : CyclicRootLift K m} {L₀ : CyclicRootLift k m}
    (j : k →+* K) (hz : j L₀.modularRoot = L.modularRoot)
    (hc : L₀.complexRoot = L.complexRoot) (C : CompleteCoefficientRing L₀)
    {τ : Representation k G (Fin n → k)} {Q : Representation K G V}
    (a : (mapCoefficients j τ).Equiv Q) (P : ResidueProjectiveLift C.residue τ) :
    IntegralLift L Q where
  Coeff := C.Coeff
  complex := C.complex
  complex_injective := C.complex_injective
  residue := j.comp C.residue
  residue_ker := by
    rw [RingHom.ker_comp_of_injective _ j.injective, C.residue_ker]
  degree := P.degree
  rep := P.rep
  projective := P.projective
  reduction := by
    rw [← mapCoefficients_comp]
    exact (coefficientEquiv j P.reduction).trans a
  root := C.root
  root_pow := C.root_pow
  root_complex := C.root_complex.trans hc
  root_residue := by
    change j (C.residue C.root) = L.modularRoot
    rw [C.root_residue, hz]

end Representation.CyclicDefect.ProjectivePairing.IntegralLifting
