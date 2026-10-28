module

public import Theory.AlgebraicGroup.Morphism.Isogeny
public import Theory.AlgebraicGroup.Semisimple.Defs

universe u

/-!
Universal and adjoint versions of semisimple algebraic groups.

The universal clause follows GLS3, Theorem 1.10.4(b) and Definition 1.10.5:
an incoming isogeny is only the witness that the source is another version of
the same semisimple group, and universality asks for an isogeny in the opposite
direction.  It does not ask for a regular section of the incoming map.  This
distinction is essential in positive characteristic, where Frobenius gives an
inseparable self-isogeny without a regular inverse.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

@[expose]
public def IsUniversalVersion
    (G : Variety k) [AlgebraicGroup G] : Prop :=
  IsSemisimpleAlgebraicGroup G ∧
    ∀ {H : Variety k} [AlgebraicGroup H]
      (_hHconnected : _root_.IsConnected (Set.univ : Set (Variety.Point H)))
      (φ : AlgebraicGroup.Morphism H G),
      IsIsogeny φ → ∃ ψ : AlgebraicGroup.Morphism G H, IsIsogeny ψ

@[expose]
public def IsAdjointVersion
    (G : Variety k) [AlgebraicGroup G] : Prop :=
  IsSemisimpleAlgebraicGroup G ∧
    ∀ {H : Variety k} [AlgebraicGroup H]
      (φ : AlgebraicGroup.Morphism G H),
      IsIsogeny φ → Function.Injective φ.onPoints

namespace IsUniversalVersion

/-- The semisimplicity field of a universal version. -/
public theorem semisimple
    {G : Variety k} [AlgebraicGroup G] (hG : IsUniversalVersion G) :
    IsSemisimpleAlgebraicGroup G :=
  hG.1

/--
The source-faithful mapping property of a universal version.  The incoming
isogeny identifies the source as another version; the returned map is an
isogeny from the universal group to that source.
-/
public theorem exists_isogeny
    {G : Variety k} [AlgebraicGroup G] (hG : IsUniversalVersion G)
    {H : Variety k} [AlgebraicGroup H]
    (hHconnected : _root_.IsConnected (Set.univ : Set (Variety.Point H)))
    (φ : AlgebraicGroup.Morphism H G) (hφ : IsIsogeny φ) :
    ∃ ψ : AlgebraicGroup.Morphism G H, IsIsogeny ψ :=
  hG.2 hHconnected φ hφ

/--
Compatibility with proofs of the former, stronger contract.  A regular left
inverse to a surjective isogeny is automatically its two-sided inverse on
points, so it is itself an isogeny.  This theorem lets existing constructions
that genuinely produce such sections establish the source-faithful predicate;
the converse is intentionally unavailable in positive characteristic.
-/
public theorem of_incoming_isogeny_sections
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsSemisimpleAlgebraicGroup G)
    (hsections : ∀ {H : Variety k} [AlgebraicGroup H],
      _root_.IsConnected (Set.univ : Set (Variety.Point H)) →
      ∀ φ : AlgebraicGroup.Morphism H G, IsIsogeny φ →
        ∃ ψ : AlgebraicGroup.Morphism G H,
          Function.LeftInverse ψ.onPoints φ.onPoints) :
    IsUniversalVersion G := by
  refine ⟨hG, ?_⟩
  intro H _ hHconnected φ hφ
  obtain ⟨ψ, hψ⟩ := hsections hHconnected φ hφ
  have hright : Function.RightInverse ψ.onPoints φ.onPoints :=
    hψ.rightInverse_of_surjective hφ.1
  refine ⟨ψ, hψ.surjective, ?_⟩
  have hker : ψ.kernel = ⊥ :=
    (MonoidHom.ker_eq_bot_iff ψ.onPoints).mpr hright.injective
  rw [hker]
  infer_instance

end IsUniversalVersion

end Theory.AlgebraicGroup
