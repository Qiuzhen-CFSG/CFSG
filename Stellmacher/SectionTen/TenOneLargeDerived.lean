module
public import Stellmacher.SectionTen.TenOneSmallCommutatorActor
public import Stellmacher.SectionTen.TenOneMiddleCenterDerived

/-!
# The neighborhood derived subgroup in the large case of (10.1)

In the actual Section Ten configuration, assume that no first-module actor
outside the terminal core is a transvection on the terminal quotient module,
and that the endpoint-module intersection has order eight. These are the
source case conditions (12) and (14), rather than any derived or generation
conclusion. Then the neighborhood derived subgroup equals that intersection,
and its quotient by the middle center has order two.

The unconditional actor selection gives a quotient commutator of order four.
The ambient actor commutator lies in the neighborhood derived subgroup,
as does the terminal center through the proved middle-center lower bound.
Their join therefore has order eight inside that derived subgroup. The common
derived upper bound puts the join inside the endpoint intersection, and equal
finite orders identify them. The final index uses the middle center's order four.

Source: Stellmacher (10.1), Journal of Algebra 190 (1997), printed pp.62–65,
`refs/files/stellmacher-n-group.pdf`. The bars mean V/Z as defined on p.59;
the source branch cardinality and absence of transvections remain explicit.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_derived
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hlarge : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ ctx.criticalPath.a' : Subgroup G) = 8)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    DerivedAmbient (GeneratedNeighborhoodV ctx.Γ middle) =
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨actor, hactor, hout, hcase⟩ := ten_one_quotient_commutator_actor ctx middle hpath
  obtain ⟨hcard, _⟩ := hcase.resolve_left (hno actor hactor hout)
  let Wnext := GeneratedNeighborhoodV ctx.Γ middle
  let D := DerivedAmbient Wnext
  let I := VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a'
  let C := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
    ZAt ctx.Γ ctx.criticalPath.a'
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hVW (vertex : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent middle vertex) :
      VAt ctx.Γ vertex ≤ Wnext :=
    le_sSup ⟨vertex, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj, rfl⟩
  have hcomm : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤ D := by
    rw [show D = ⁅Wnext, Wnext⁆ from Subgroup.map_subtype_commutator Wnext]
    exact Subgroup.commutator_mono (hVW _ hterminal)
      ((Subgroup.zpowers_le.mpr hactor).trans (hVW _ hfirst))
  have hZD : ZAt ctx.Γ ctx.criticalPath.a' ≤ D := by
    apply le_trans ?_ (ten_one_middle_center_le_neighborhood_derived ctx middle hpath)
    rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
    exact le_sup_right
  have hCD : C ≤ D := sup_le hcomm hZD
  have hDI : D ≤ I := ten_one_generated_derived_le_intersection ctx middle hpath
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨mover, _, hmover⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hZcard := (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext hb
    ctx.criticalPath.a' ⟨mover, hmover⟩).1
  have hCcard : Nat.card C = 8 := by
    change Nat.card C = 4 * Nat.card (ZAt ctx.Γ ctx.criticalPath.a') at hcard
    simpa only [hZcard] using hcard
  have hCI : C = I := Subgroup.eq_of_le_of_card_ge (hCD.trans hDI)
    (by rw [hCcard]; exact hlarge.le)
  change D = I
  exact le_antisymm hDI (hCI ▸ hCD)

public theorem ten_one_large_derived_center_index
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hlarge : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ ctx.criticalPath.a' : Subgroup G) = 8)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    QuotientCardEq (DerivedAmbient (GeneratedNeighborhoodV ctx.Γ middle))
      (ZAt ctx.Γ middle) 2 := by
  change Nat.card (DerivedAmbient (GeneratedNeighborhoodV ctx.Γ middle)) =
    2 * Nat.card (ZAt ctx.Γ middle)
  rw [ten_one_large_derived ctx middle hpath hlarge hno, hlarge,
    (sectionTenOpeningData ctx middle hpath).center_card]

end Stellmacher.SectionTen
