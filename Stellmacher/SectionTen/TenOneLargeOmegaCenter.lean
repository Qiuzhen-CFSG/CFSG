module
public import Stellmacher.SectionTen.TenOneLargeOmegaFixedComponent
public import Stellmacher.SectionTen.TenOneLargeOmegaFixedContradiction

/-!
# The neighborhood omega center in the large branch

In the actual no-transvection Section Ten configuration, the omega-one center
of the generated neighborhood equals the common first/terminal module
intersection. This is the valid omega-center conclusion in source (16).

The fixed-component construction factors the omega center as the common
intersection joined with its terminal-residual-fixed component. The exact
commutator-family bound makes that component fit the affine four-point
centralizer argument: a point outside the terminal center would have
transitive centralizers at adjacent vertices, contradicting native (7.2).
Thus the component lies in the terminal center, which is already in the
common intersection. The reverse containment is the established setup bound.

Source: Stellmacher (10.1)(16), printed p.64 of
`refs/files/stellmacher-n-group.pdf`. The printed additional equality for
C_W(V_terminal) is inconsistent with the proved order-sixteen intersection;
this theorem proves only the valid omega-center claim, with the original
context and no-transvection hypothesis and no later classification premise.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_neighborhood_omega_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle)=
      VAt ctx.Γ ctx.criticalPath.firstStep⊓VAt ctx.Γ ctx.criticalPath.a' := by
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Z:=ZAt ctx.Γ ctx.criticalPath.a'
  let I:=VAt ctx.Γ ctx.criticalPath.firstStep⊓V
  let O:=omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle)
  let W:=conjugateClosure (VAt ctx.Γ ctx.criticalPath.firstStep⊓QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ middle)
  let Y:=(W⊓Subgroup.centralizer (V:Set G))⊔O
  let D:=(Y⊔V)⊓Subgroup.centralizer (EAt ctx.Γ ctx.criticalPath.a':Set G)
  obtain ⟨_hsplit,hDO,hOeq,hPD,hDV⟩:=ten_one_large_omega_fixed_component ctx middle hpath hno
  have hOU : ⁅O,twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⁆≤Z:=
    (Subgroup.commutator_mono (show O≤Y⊔V from le_sup_right.trans le_sup_left) le_rfl).trans
      (ten_one_large_centralizer_core_commutator ctx middle hpath hno)
  have hDZ : D≤Z:=ten_one_large_omega_fixed_subgroup_le_center ctx middle hpath hno D hDO inf_le_right hPD hDV hOeq hOU
  obtain ⟨_,hfirst,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hZI : Z≤I:=by
    have hmid:ZAt ctx.Γ middle≤I:=le_inf
      (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst))
      (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hterminal))
    apply le_trans ?_ hmid
    rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
    exact le_sup_right
  exact le_antisymm (hOeq.le.trans (sup_le le_rfl (hDZ.trans hZI)))
    (ten_one_large_centralizer_setup ctx middle hpath hno).2.2.2.2.2.2.1
end Stellmacher.SectionTen
