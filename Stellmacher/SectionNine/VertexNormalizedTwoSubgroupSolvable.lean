module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_1

/-!
# Solvable normalizers of two-subgroups normalized by a vertex stabilizer

In the ambient Section Nine context, a nontrivial two-subgroup L normalized
by a vertex stabilizer has solvable ambient normalizer N_H(L.map embedding).
Its local normalizer N_G(L) is consequently solvable. The conclusion uses
Hypothesis Two only on the original ambient group H.

Conjugate the vertex stabilizer to one of the two base stabilizers. Its
conjugated embedded image contains the supplied subgroup S, because T lies
in either base and its embedding is exactly S. Thus the conjugated ambient
normalizer contains Baumann(S); it is a two-local subgroup by the explicit
nontrivial two-subgroup witness. Hypothesis Two's local_B condition makes
that normalizer solvable. Injective conjugation returns the ambient result,
and the embedding restricts injectively to the local normalizer.

This is the normalizer-solvability consequence of Hypothesis Two used in
Stellmacher (10.1), Journal of Algebra 190 (1997), printed p.63, between
(13) and (14). It also applies to the small-branch normalizer arguments.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ambient_vertex_normalized_two_subgroup_solvable
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (vertex : ctx.Γ.Vertex) (L : Subgroup G)
    (hne : L ≠ ⊥) (hL : IsPGroup 2 L)
    (hnorm : GAt ctx.Γ vertex ≤ Subgroup.normalizer (L : Set G)) :
    Group.IsSolvable (Subgroup.normalizer (L.map embedding : Set H)) := by
  obtain ⟨g, hg⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).vertex_stabilizers_conjugate vertex
  let c : MulAut H := MulAut.conj (embedding g)⁻¹
  let f : G →* H := c.toMonoidHom.comp embedding
  have hf : Function.Injective f := c.injective.comp ctx.embedding_injective
  let K := L.map f
  let N := Subgroup.normalizer (K : Set H)
  have hKne : K ≠ ⊥ := by
    intro hbot
    apply hne
    apply bot_unique
    intro x hx
    have hfx : f x ∈ K := Subgroup.mem_map_of_mem f hx
    rw [hbot,Subgroup.mem_bot] at hfx
    exact Subgroup.mem_bot.mpr (hf (hfx.trans (map_one f).symm))
  have hlocal : IsTwoLocal N := ⟨K,hKne,hL.map f,rfl⟩
  have hT : (T.map (MulAut.conj g).toMonoidHom) ≤ GAt ctx.Γ vertex := by
    rcases hg with hA | hB
    · rw [GAt,hA]
      exact Subgroup.map_mono ctx.sectionSeven.P1_mem.1.2.1.1
    · rw [GAt,hB]
      exact Subgroup.map_mono ctx.sectionSeven.P2_mem.1.2.1.1
  have hSP : S ≤ (GAt ctx.Γ vertex).map f := by
    intro s hs
    have hs' : s ∈ T.map embedding := ctx.map_S.symm ▸ hs
    obtain ⟨t,ht,rfl⟩ := hs'
    refine ⟨g*t*g⁻¹, hT (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ht), ?_⟩
    change (embedding g)⁻¹ * embedding (g*t*g⁻¹) * ((embedding g)⁻¹)⁻¹ = embedding t
    simp only [map_mul,map_inv,inv_inv]
    group
  have hSN : S ≤ N := hSP.trans
    ((Subgroup.map_mono hnorm).trans (Subgroup.le_normalizer_map f))
  let _ : Group.IsSolvable N := (ctx.hypothesisTwo.local_B N hlocal
    ((show baumannIn S ≤ S from inf_le_left).trans hSN)).1
  have hK : (L.map embedding).map c.toMonoidHom = K := by
    rw [Subgroup.map_map]
  let M := Subgroup.normalizer (L.map embedding : Set H)
  have hMN : M.map c.toMonoidHom ≤ N := by
    have hh := Subgroup.le_normalizer_map (H := L.map embedding) c.toMonoidHom
    rwa [hK] at hh
  let into : M →* N := (c.toMonoidHom.comp M.subtype).codRestrict N
    (fun x => hMN (Subgroup.mem_map_of_mem c.toMonoidHom x.property))
  have hinj : Function.Injective into := by
    intro x y heq
    apply Subtype.ext
    exact c.injective (congrArg Subtype.val heq)
  exact Group.isSolvable_of_isSolvable_injective hinj

public theorem vertex_normalized_two_subgroup_solvable
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (vertex : ctx.Γ.Vertex) (L : Subgroup G)
    (hne : L ≠ ⊥) (hL : IsPGroup 2 L)
    (hnorm : GAt ctx.Γ vertex ≤ Subgroup.normalizer (L : Set G)) :
    Group.IsSolvable (Subgroup.normalizer (L : Set G)) := by
  let M := Subgroup.normalizer (L : Set G)
  let N := Subgroup.normalizer (L.map embedding : Set H)
  let _ : Group.IsSolvable N :=
    ambient_vertex_normalized_two_subgroup_solvable ctx vertex L hne hL hnorm
  let into : M →* N := (embedding.comp M.subtype).codRestrict N
    (fun x => Subgroup.le_normalizer_map embedding (Subgroup.mem_map_of_mem embedding x.property))
  have hinj : Function.Injective into := by
    intro x y heq
    apply Subtype.ext
    exact ctx.embedding_injective (congrArg Subtype.val heq)
  exact Group.isSolvable_of_isSolvable_injective hinj

end Stellmacher.SectionNine
