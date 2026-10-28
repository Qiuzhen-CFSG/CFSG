module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve.Source
public import Theory.Representation.FirstCohomologyDuality

/-!
# Removing the central kernel of a natural quotient

A commutator-generated central cover is a quotient of the universal cover.
When dual first cohomology vanishes, the universal projection is injective,
so every such cover is injective. Applying this to the *given* fixed-space
quotient identifies the whole module with one natural summand. No such
vanishing is imposed on the six-dimensional orthogonal module.

Source: Aschbacher–Smith, I.1.5 and I.1.6(6), printed p.408, as used in
B.5.1(1), pp.99–102.
-/

public section

open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve
open Chapter2.ComponentRefinement.LieType.Binary

/-- Zero dual H¹ makes every perfect central covering map injective. -/
theorem cover_injective_of_dual_H1_zero
    {k H N W : Type*} [Field k] [Group H] [Finite H]
    [AddCommGroup N] [Module k N] [FiniteDimensional k N]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {τ : Representation k H N} {σ : Representation k H W}
    (p : σ.IntertwiningMap τ) (hp : IsCover p)
    (hH : Module.finrank k (H1 τ.dual) = 0) : Function.Injective p := by
  obtain ⟨q, hq, heq⟩ := exists_universalCover_quotient p hp
  have hu : Function.Injective (universalCoverProjection τ) := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    rw [finrank_ker_universalCoverProjection, hH]
  intro x y hxy
  obtain ⟨a, rfl⟩ := hq x
  obtain ⟨b, rfl⟩ := hq y
  apply congrArg q
  apply hu
  rw [← heq, ← heq, hxy]

variable {K V : Type*} [Group K] [Finite K]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {ρ : Representation (ZMod 2) K V} {L : Subgroup K}

omit [Finite K] in
/-- Transport the precise dual cohomology calculation through the component model. -/
theorem natural_dual_H1_zero (cohomology : UniversalNaturalCohomology)
    (model : L ≃* PSL 4) :
    Module.finrank (ZMod 2) (H1 (Representation.dual
      ((natural 4).comp model.toMonoidHom))) = 0 := by
  let e := H1Congr (Representation.dual ((natural 4).comp model.toMonoidHom)) (natural 4).dual
    model (LinearEquiv.refl (ZMod 2) (Module.Dual (ZMod 2) (Vector 4)))
    (by
      intro g φ
      apply LinearMap.ext
      intro v
      change φ (natural 4 (model g⁻¹) v) = φ (natural 4 ((model g)⁻¹) v)
      rw [map_inv])
  rw [e.finrank_eq]
  exact cohomology 4 (Or.inl rfl)

/-- A natural quotient is the whole module when `[V,L]=V`. This proves the
central-cover splitting; the coordinates on the quotient alone do not suffice. -/
theorem NaturalQuotient.repeated_one (h : NaturalQuotient ρ L 4)
    (full : Coinvariants.ker (ρ.comp L.subtype) = ⊤)
    (cohomology : UniversalNaturalCohomology) : Nonempty (RepeatedNatural ρ L 1) := by
  let τ : Representation (ZMod 2) L (Vector 4) := (natural 4).comp h.model.toMonoidHom
  let p : Representation.IntertwiningMap (ρ.comp L.subtype) τ :=
    (h.coordinates.toLinearMap.comp (fixedSpace ρ L).mkQ).intertwiningMap_of_isIntertwiningMap
      _ _ h.equivariant
  have hs : Function.Surjective p :=
    h.coordinates.surjective.comp (Submodule.mkQ_surjective _)
  have hp : IsCover p := by
    refine ⟨hs, ?_, full⟩
    intro v hv
    have hz : (fixedSpace ρ L).mkQ v = 0 := by
      apply h.coordinates.injective
      exact hv.trans (map_zero h.coordinates).symm
    have hf : v ∈ fixedSpace ρ L := (Submodule.Quotient.mk_eq_zero _).mp hz
    exact hf
  let E := LinearEquiv.ofBijective p.toLinearMap
    ⟨cover_injective_of_dual_H1_zero p hp (natural_dual_H1_zero cohomology h.model), hs⟩
  refine ⟨{ model := h.model
            coordinates := E.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Vector 4)).symm
            equivariant := ?_ }⟩
  intro l v i
  exact h.equivariant l v

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve

end
