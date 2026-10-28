module

public import Stellmacher.SectionsOneToFourDefs

/-!
# Injective transport of internal product families

An injective group homomorphism preserves the defining generation,
pairwise disjointness, and pairwise commutation of an internal direct
product family. The index type is unchanged, and no stronger independence
claim is assumed or inferred.

Mapping the supremum gives generation; injectivity preserves disjointness;
mapping the commuting equations gives the final field. This is used to
transport the Option-indexed intrinsic module product into the ambient
group in Stellmacher (2.2), Journal of Algebra 190 (1997), p.20, in
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher

public theorem IsInternalDirectProductFamily.map_injective
    {G H ι : Type*} [Group G] [Group H]
    {E : Subgroup G} {K : ι → Subgroup G}
    (h : IsInternalDirectProductFamily E K) (f : G →* H)
    (hf : Function.Injective f) :
    IsInternalDirectProductFamily (E.map f) (fun i => (K i).map f) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h.1, Subgroup.map_iSup]
  · intro i j hij
    exact Subgroup.disjoint_map hf (h.2.1 i j hij)
  · intro i j hij x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    simpa using congrArg f (h.2.2 i j hij x₀ hx₀ y₀ hy₀)

end Stellmacher
