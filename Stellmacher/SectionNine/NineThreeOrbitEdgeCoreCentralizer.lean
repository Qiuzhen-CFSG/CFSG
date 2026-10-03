module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Theory.GroupTheory.SubgroupConjugation


/-!
# Neighboring-core centralizers on the initial vertex orbit

For the actual Section Nine local context, any two-subgroup in a stabilizer
at an initial-orbit vertex that centralizes its center lies in its two-core.
In particular, the part of a neighboring core centralizing that center lies
in the first vertex core. The general form also supplies the conjugated
neighborhood-join input to the geometric extraction in (9.8).

First extend the equality `S ∩ C_G(Z_a) = Q_a` from (7.4) to every
local two-subgroup centralizing `Z_a`. Embed such a subgroup in an intrinsic
Sylow subgroup of `G_a` and conjugate that Sylow to the distinguished one.
Both the center centralizer and the vertex core are normalized by `G_a`,
so (7.4) applies after conjugation and transports back. The supplied vertex
conjugacy transports stabilizers, centers, and cores to `a`; the general
two-subgroup bound follows. Adjacency and (7.3) put a neighboring core inside
`G_d`, giving the original neighboring-core theorem as a wrapper.

This is the second fixed-subgroup containment in the neighboring core used
in Stellmacher (9.3), Journal of Algebra 190 (1997), p.49. It requires no
terminal classification and no restriction of the critical length to three.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix

private theorem initial_pgroup_centralizer
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionNineLocalContext G S P1 P2)
    (U : Subgroup G) (hU : IsPGroup 2 U)
    (hUP : U ≤ stabilizer ctx.Γ ctx.criticalPath.a)
    (hUC : U ≤ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G)) :
    U ≤ q ctx.Γ ctx.criticalPath.a := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let C := Subgroup.centralizer (z Γ cp.a : Set G)
  obtain ⟨_, T, hT⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).1
  obtain ⟨V, hV⟩ := (hU.comap_of_injective P.subtype P.subtype_injective).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P T V
  have hconj : (T : Subgroup P).map (MulAut.conj g).toMonoidHom = (V : Subgroup P) :=
    congrArg Sylow.toSubgroup hg
  have hPC : P ≤ Subgroup.normalizer (C : Set G) :=
    (stabilizer_le_normalizer_z Γ cp.a).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (z Γ cp.a : Set G))).mp inferInstance)
  have hPQ := stabilizer_le_normalizer_q Γ cp.a
  intro u hu
  let uP : P := ⟨u, hUP hu⟩
  have huV : uP ∈ (V : Subgroup P) := hV hu
  rw [← hconj] at huV
  obtain ⟨a, ha, hea⟩ := huV
  have heaG : (g : G) * (a : G) * (g : G)⁻¹ = u := congrArg Subtype.val hea
  have haS : (a : G) ∈ S := hT ▸ Subgroup.mem_map_of_mem P.subtype ha
  have haC : (a : G) ∈ C :=
    (Subgroup.mem_normalizer_iff.mp (hPC g.property) (a : G)).mpr (heaG ▸ hUC hu)
  have haQ : (a : G) ∈ q Γ cp.a :=
    (lemma_seven_four ctx.sectionSeven Γ cp).edge_centralizer ▸ ⟨haS, haC⟩
  have hgaQ := (Subgroup.mem_normalizer_iff.mp (hPQ g.property) (a : G)).mp haQ
  exact heaG ▸ hgaQ

/-- A two-subgroup centralizing an initial-orbit center lies in that vertex's core. -/
public theorem nine_three_orbit_pgroup_centralizer
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionNineLocalContext G S P1 P2)
    (d : ctx.Γ.Vertex) (hd : IsConjugateVertex ctx.Γ ctx.criticalPath.a d)
    (U : Subgroup G) (hU2 : IsPGroup 2 U)
    (hUP : U ≤ stabilizer ctx.Γ d)
    (hUC : U ≤ Subgroup.centralizer (z ctx.Γ d : Set G)) :
    U ≤ q ctx.Γ d := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  obtain ⟨g, hg⟩ := hd
  have hGd : (stabilizer Γ d).conjBy g = stabilizer Γ cp.a := by
    rw [← hg, stabilizer_act]
    change ((stabilizer Γ cp.a).conjBy g⁻¹).conjBy g = _
    exact Subgroup.conjBy_inv' _ _
  have hZd : (z Γ d).conjBy g = z Γ cp.a := by
    rw [← hg, z_act]
    exact Subgroup.conjBy_inv' _ _
  have hQd : (q Γ d).conjBy g = q Γ cp.a := by
    rw [← hg, q_act]
    exact Subgroup.conjBy_inv' _ _
  have hconjP : U.conjBy g ≤ stabilizer Γ cp.a := by
    rw [← hGd]
    exact Subgroup.map_mono hUP
  have hconjC : U.conjBy g ≤ Subgroup.centralizer (z Γ cp.a : Set G) := by
    have hh := (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
      hUC).trans
      (Subgroup.map_centralizer_le_centralizer_image (z Γ d : Set G)
        (MulAut.conj g).toMonoidHom)
    change U.conjBy g ≤ Subgroup.centralizer ((z Γ d).conjBy g : Set G) at hh
    rwa [hZd] at hh
  have hbound := initial_pgroup_centralizer ctx (U.conjBy g)
    (hU2.map (MulAut.conj g).toMonoidHom) hconjP hconjC
  rw [← hQd] at hbound
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective).mp hbound

/-- A neighboring core centralizing the center at an initial-orbit vertex
lies in that vertex's own core. -/
public theorem nine_three_orbit_edge_core_centralizer
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionNineLocalContext G S P1 P2)
    (d : ctx.Γ.Vertex) (hd : IsConjugateVertex ctx.Γ ctx.criticalPath.a d)
    (n : ctx.Γ.Vertex) (hn : n ∈ neighborhood ctx.Γ d) :
    q ctx.Γ n ⊓ Subgroup.centralizer (z ctx.Γ d : Set G) ≤ q ctx.Γ d := by
  let Γ := ctx.Γ
  let U := q Γ n ⊓ Subgroup.centralizer (z Γ d : Set G)
  have hUn : U ≤ q Γ n := inf_le_left
  have hU2 : IsPGroup 2 U := by
    have hQ2 : IsPGroup 2 (q Γ n) := by
      rw [q, Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := stabilizer Γ n)).map _
    exact hQ2.to_le hUn
  have hUP : U ≤ stabilizer Γ d := hUn.trans
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core n d
      ((mem_neighborhood_iff_adjacent Γ).mpr
        (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hn))) default).2.2)
  exact nine_three_orbit_pgroup_centralizer ctx d hd U hU2 hUP inf_le_right

end Stellmacher.SectionNine
