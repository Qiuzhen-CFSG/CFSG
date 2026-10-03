module

public import Stellmacher.SectionNine.NineSevenNormalityObstructions
public import Stellmacher.SectionNine.NineSevenShiftedIntersections

/-!
# A cubic covariant-family kernel

Two-transitivity and the absence of a common normal 2-subgroup force a
nontrivial, covariant family of vertex-normalized 2-subgroups to distinguish
the neighbors. A vertex subgroup normalizing all of them therefore belongs
to the kernel of the cubic neighbor action. Equality of two neighboring
members propagates along ordered neighbor pairs and produces a nontrivial
2-subgroup normalized by both edge stabilizers, contradicting the trivial
ambient two-core. The cubic action identifies the resulting pointwise
neighbor kernel with the vertex two-core.

Source: Stellmacher (9.7), printed p.54 / PDF p.44, the implications from
commutator containment to normality of neighboring V or W groups.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem neighboring_family_injective
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h7 : SectionSevenHypotheses G T A B) (Gamma : CosetGraphContext G T A B)
    (vertex : Gamma.Vertex)
    (hmodel : QuotientIsModel (GAt Gamma vertex) (QAt Gamma vertex) SL2Two)
    (family : Gamma.Vertex → Subgroup G)
    (hcov : ∀ actor point, family (Gamma.act actor point) =
      (family point).map (MulAut.conj actor⁻¹).toMonoidHom)
    (hown : ∀ point, GAt Gamma point ≤ Subgroup.normalizer (family point : Set G))
    (htwo : ∀ point, Gamma.adjacent vertex point → IsPGroup 2 (family point))
    (hne : ∀ point, Gamma.adjacent vertex point → family point ≠ ⊥)
    {left right : Gamma.Vertex}
    (hleft : Gamma.adjacent vertex left) (hright : Gamma.adjacent vertex right)
    (heq : family left = family right) : left = right := by
  by_contra hdistinct
  have hsame (point : Gamma.Vertex) (hpoint : Gamma.adjacent vertex point) :
      family point = family left := by
    by_cases hpointLeft : point = left
    · rw [hpointLeft]
    obtain ⟨mover, hmoveLeft, _, hmoveRight⟩ := nine_seven_two_arc_transport h7 Gamma
      hleft hright hdistinct hleft hpoint (Ne.symm hpointLeft)
      ⟨1, Gamma.act_one _⟩ hmodel
    have hmap := congrArg (fun subgroup : Subgroup G =>
      subgroup.map (MulAut.conj mover⁻¹).toMonoidHom) heq
    rw [← hcov, ← hcov, hmoveLeft, hmoveRight] at hmap
    exact hmap.symm
  have hnormal : GAt Gamma vertex ≤ Subgroup.normalizer (family left : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro actor hactor element helement
    have hfix : Gamma.act actor⁻¹ vertex = vertex :=
      (Set.ext_iff.mp (Gamma.stabilizer_def vertex) actor⁻¹).mp
        ((GAt Gamma vertex).inv_mem hactor)
    have hadj := adjacent_act Gamma actor⁻¹ hleft
    rw [hfix] at hadj
    have hmap : (family left).map (MulAut.conj actor).toMonoidHom = family left := by
      have hact := hcov actor⁻¹ left
      simp only [inv_inv] at hact
      rw [← hact]
      exact hsame _ hadj
    exact hmap ▸ Subgroup.mem_map_of_mem (MulAut.conj actor).toMonoidHom helement
  exact hne left hleft (nine_seven_edge_invariant_two_subgroup_eq_bot h7 Gamma hleft
    (family left) (htwo left hleft) hnormal (hown left))

public theorem nine_seven_cubic_family_kernel
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h7 : SectionSevenHypotheses G T A B) (Gamma : CosetGraphContext G T A B)
    (vertex : Gamma.Vertex)
    (hmodel : QuotientIsModel (GAt Gamma vertex) (QAt Gamma vertex) SL2Two)
    (family : Gamma.Vertex → Subgroup G)
    (hcov : ∀ actor point, family (Gamma.act actor point) =
      (family point).map (MulAut.conj actor⁻¹).toMonoidHom)
    (hown : ∀ point, GAt Gamma point ≤ Subgroup.normalizer (family point : Set G))
    (htwo : ∀ point, Gamma.adjacent vertex point → IsPGroup 2 (family point))
    (hne : ∀ point, Gamma.adjacent vertex point → family point ≠ ⊥)
    (actors : Subgroup G) (hactors : actors ≤ GAt Gamma vertex)
    (hnormalizes : ∀ point, Gamma.adjacent vertex point →
      actors ≤ Subgroup.normalizer (family point : Set G)) :
    actors ≤ QAt Gamma vertex := by
  intro actor hactor
  apply ((cubic_local_action_of_sl2Two_quotient Gamma h7 vertex hmodel).kernel
    ⟨actor, hactors hactor⟩).mpr
  intro point hpoint
  have hfix : Gamma.act actor vertex = vertex :=
    (Set.ext_iff.mp (Gamma.stabilizer_def vertex) actor).mp (hactors hactor)
  have hadj := adjacent_act Gamma actor hpoint
  rw [hfix] at hadj
  apply neighboring_family_injective h7 Gamma vertex hmodel family hcov hown htwo hne
    hadj hpoint
  rw [hcov]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normalizer (family point : Set G)).inv_mem
      (hnormalizes point hpoint hactor))

end Stellmacher.SectionNine

