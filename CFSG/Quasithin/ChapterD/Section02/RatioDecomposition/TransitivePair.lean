module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.TransitiveFactors
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SupportProjectionSeed
/-!
# The original Sylow subgroup on a transitive pair

Conjugate literal supports have equal dimension. Once the factor family has
two members, a support stabilizer is normal of index dividing two and
supplements every Sylow two-subgroup. Transitivity therefore already holds
under the original Sylow subgroup, on the unchanged factor indices.

Source: Aschbacher--Smith 15.1.2(3), printed p.1086.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)
namespace FactorData
omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem transitive_factor_dimensions
    (π : G →* Equiv.Perm d.Index)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space)
    (ht : ∀ i j, ∃ g : G, π g i = j) (i j : d.Index) :
    Module.finrank (ZMod 2) (d.factor i).Space =
      Module.finrank (ZMod 2) (d.factor j).Space := by
  have hd (k : d.Index) : Module.finrank (ZMod 2) (d.factor k).Space =
      Module.finrank (ZMod 2) (c.ambientFactor d k).space := by
    let a : (d.factor k).Space →ₗ[ZMod 2] V := U.subtype.comp (d.factor k).embedding.spaceMap
    let e : (d.factor k).Space ≃ₗ[ZMod 2] (c.ambientFactor d k).space :=
      LinearEquiv.ofInjective a (U.subtype_injective.comp (d.factor k).embedding.space_injective)
    exact e.finrank_eq
  obtain ⟨g,hg⟩ := ht i j
  rw [hd i,hd j,←hg,←hs]
  exact ((LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)).finrank_map_eq _).symm

omit [FiniteDimensional (ZMod 2) V] in
theorem transitive_pair_sylow
    (π : G →* Equiv.Perm d.Index)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space)
    (ht : ∀ i j, ∃ g : G, π g i = j) (hc : Nat.card d.Index = 2)
    (P : Sylow 2 G) (i j : d.Index) : ∃ t : G, t ∈ (P : Subgroup G) ∧ π t i = j := by
  let N := subspaceStabilizer ρ (c.ambientFactor d i).space
  let := c.ambient_space_stabilizer_normal_of_count d π hs hc.le i
  have hgen : (P : Subgroup G) ⊔ N = ⊤ := c.support_stabilizer_sylow_supplement d π hs hc.le P i
  obtain ⟨g,hg⟩ := ht i j
  obtain ⟨t,ht,n,hn,rfl⟩ := mem_sup_of_normal_right.mp (hgen ▸ mem_top g)
  have hni : π n i = i := by
    have he := (subspace_map_eq_iff ρ (c.ambientFactor d i).space n).mpr hn
    rw [hs] at he
    exact (c.ambient_spaces_independent d).injective (c.ambient_space_ne_bot d) he
  refine ⟨t,ht,?_⟩
  simpa only [map_mul,Equiv.Perm.mul_apply,hni] using hg
end FactorData
end CFSG.Quasithin.ChapterD.RatioDecomposition
