module

public import Theory.Representation.SU3.CubicDegree.InnerActors.RootControl
public import Theory.Representation.SU3.CubicDegree.InnerActors.ThreeRoots

/-!
# The inner-actor degree bound for binary SU₃

An elementary actor in the linear image lifts through the odd central action
kernel. Root control places its lift in a Sylow center of order `2^s` and
offender maximization gives that center fixed codimension at most `2*s`.
Three conjugate Sylow centers generate the full special unitary group, so
their fixed spaces have zero intersection and the degree is at most `6*s`.

Both concrete root-geometric inputs are discharged here. The argument retains
arbitrary Hermitian forms, `s = 2`, and possible central action kernels;
cubicity is unnecessary. The literal source cover is the consumer in
`UnitaryRecognition.CubicDegree.InnerActors`.

Source: Aschbacher--Smith K.3.3, printed p.456 under the hypotheses on
p.451; Guralnick--Malle, Classification of 2F-modules II, Lemma 2.1,
and Huppert II.10.12 for the Hermitian root geometry.
-/

public section
open BenderSuzuki.MatrixGroups Representation.BinaryOffender Subgroup
namespace Representation.SU3.CubicDegree.InnerActors

/-- An inner elementary actor of ratio at most two bounds the binary degree
by `6*s`, including cubic actors and actions with nontrivial central kernel. -/
theorem finrank_le_of_inner_actor
    {F V : Type*} [Field F] [Finite F]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (σ : Representation (ZMod 2) J.specialSubgroup V) (hi : σ.IsIrreducible)
    (hk : σ.ker ≤ center J.specialSubgroup)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hc : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A)
    (hinner : A ≤ (actionImage σ).subgroupOf (linearNormalizer σ)) :
    Module.finrank (ZMod 2) V ≤ 6 * s :=
  finrank_le_of_inner_actor_of_root_geometry J hs hcard hconj
    (root_control J hs hcard hconj) (ThreeRoots.generation J hs hcard hconj)
    σ hi hk A hA hc hinner

end Representation.SU3.CubicDegree.InnerActors
