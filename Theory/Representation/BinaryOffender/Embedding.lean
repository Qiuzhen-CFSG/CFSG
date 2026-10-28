module

public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Offenders restricted along equivariant embeddings

An injective equivariant linear map induces an injection on the quotients
by fixed vectors. Fixed codimension therefore cannot increase on the smaller
module. An injective map of actors preserves elementary subgroups and their
ranks, transporting every offender to the smaller module's action.

Source: the invariant-submodule inequality in Aschbacher–Smith B.1.5(8),
combined manuscript of 1 March 2004, printed pp.69–70; used for W_K and U_K
in the central branch of 13.6.20, printed p.931.
-/

public section

namespace Representation.BinaryOffender
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
  (f : G →* D) (e : W →ₗ[ZMod 2] V) (he : Function.Injective e)
  (hact : ∀ g w, ρ g (e w) = e (σ (f g) w))

include e he hact

theorem fixedCodim_map_le_of_embedding [FiniteDimensional (ZMod 2) V]
    (A : Subgroup G) : fixedCodim σ (A.map f) ≤ fixedCodim ρ A := by
  have hc : (fixedSpace ρ A).comap e = fixedSpace σ (A.map f) := by
    ext w
    exact embedding_mem_fixedSpace_iff ρ σ f e he hact A w
  let q := (fixedSpace σ (A.map f)).mapQ (fixedSpace ρ A) e hc.ge
  have hi : Function.Injective q := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ, hc, Submodule.mkQ_map_self]
  exact LinearMap.finrank_le_finrank_of_injective hi

theorem IsOffender.map_of_embedding [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective f) {A : Subgroup G} (hA : IsOffender ρ A) :
    IsOffender σ (A.map f) := by
  let : IsElementaryAbelian 2 A := hA.1.2
  refine ⟨⟨?_, IsElementaryAbelian.map f⟩, ?_⟩
  · intro hb
    apply hA.1.1
    apply Subgroup.map_injective hf
    simpa only [Subgroup.map_bot] using hb
  · rw [rank_map_injective f hf]
    exact (fixedCodim_map_le_of_embedding ρ σ f e he hact A).trans hA.2
end Representation.BinaryOffender
