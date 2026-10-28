module

public import Theory.Representation.SU3.CubicDegree.InnerActors.RootControl
public import Theory.Representation.SU3.CubicDegree.InnerActors.Reduction

/-!
# The inner SU₃ degree bound with concrete root control

The Sylow-center placement and normalizer irreducibility premises of the
inner-actor estimate are discharged for every finite quadratic binary field
and every ternary Hermitian form. Only generation by three conjugate root
groups remains explicit; it is independent of the root-control argument.

Source: Guralnick--Malle, Classification of 2F-modules II, Lemma 2.1;
Aschbacher--Smith K.3.3, printed p.456, under the hypotheses on p.451.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups Representation Representation.BinaryOffender
namespace Representation.SU3.CubicDegree.InnerActors

/-- The concrete SU₃ root theorem discharges root control in the inner-actor
estimate, retaining just the independent three-root generation premise. -/
theorem finrank_le_of_inner_actor_of_three_root_generation
    {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (hg : ThreeRootGeneration J.specialSubgroup)
    (σ : Representation (ZMod 2) J.specialSubgroup V) (hi : σ.IsIrreducible)
    (hk : σ.ker ≤ center J.specialSubgroup)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hc : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A)
    (hinner : A ≤ (actionImage σ).subgroupOf (linearNormalizer σ)) :
    Module.finrank (ZMod 2) V ≤ 6 * s :=
  finrank_le_of_inner_actor_of_root_geometry J hs hcard hconj
    (root_control J hs hcard hconj) hg σ hi hk A hA hc hinner

end Representation.SU3.CubicDegree.InnerActors
