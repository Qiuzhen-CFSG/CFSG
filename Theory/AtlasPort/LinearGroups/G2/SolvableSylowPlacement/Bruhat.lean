module

public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement.Cells
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement.Bruhat.WeylGeometry
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement.Bruhat.RankOne

/-!
# Bruhat coverage for the full split-octonion G₂ model

Every automorphism has a factorization `u * weylRep i * t * v`, with both
outer factors in the six positive root groups and the middle factor in the
actual split torus. The proof first reduces the image of the first singular
vector using positive roots, obtaining six cells modulo its full point
stabilizer. The two-cell SL₂ calculation in that stabilizer supplies the
remaining reflection; its positive root is absorbed into the left factor.
The resulting words are exactly the twelve representatives in `Cells`.

This proves the existence part needed from GLS III, Theorem 2.3.5 and the
proof of 2.6.7 (`refs/KGroup/GLS3/chapter2.tex`), for the larger-field paragraph
after (k) on Aschbacher–Smith, printed p.1144. It neither asserts uniqueness
nor restricts the right unipotent factor. The theorem holds over every field
of characteristic two, including F₄ and F₂, on the full automorphism model.

The coordinate model and root maps come from the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.SolvableSylowPlacement
open BruhatGeometry
variable {F : Type*} [Field F] [CharP F 2]

/-- Every split-octonion automorphism lies in one of the twelve concrete Weyl cells. -/
theorem bruhatCover : BruhatCover F := by
  intro g
  obtain ⟨i,u,hu,p,hp,hg⟩ := point_cells g
  rcases parabolic_two_cells p hp with hb | ⟨a,b,hb,he⟩
  · obtain ⟨t,ht,v,hv,hp⟩ := borel_torus_unipotent p hb
    refine ⟨pointWeylIndex i,u,hu,t,ht,v,hv,?_⟩
    rw [hg,hp,← pointRep_eq_weylRep]
    group
  · obtain ⟨z,hz,hzrep⟩ := pointRep_rootE i a
    obtain ⟨t,ht,v,hv,hb⟩ := borel_torus_unipotent b hb
    refine ⟨extendedWeylIndex i,u*z,unipotent.mul_mem hu hz,t,ht,v,hv,?_⟩
    rw [hg,he,hb,← pointRep_mul_weylR]
    calc
      _ = u * (pointRep i * rootE a) * weylR * t * v := by group
      _ = (u*z) * (pointRep i * weylR) * t * v := by rw [hzrep]; group

end Atlas.G2.SolvableSylowPlacement
