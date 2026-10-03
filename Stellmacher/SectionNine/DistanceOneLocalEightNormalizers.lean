module

public import Stellmacher.SectionNine.DistanceOneVstarContainments
public import Stellmacher.SectionNine.DistanceOneSelectedEight
public import Stellmacher.SectionNine.DistanceOneTerminalEightNormalizer
public import Stellmacher.SectionNine.DistanceOneInitialEightNormalizer

/-!
# The elementary eight and its two local symmetric-four quotients

At critical distance one, the faithful-action and local-structure conclusions
allow selection of an elementary subgroup of order eight in the exact terminal
conjugate closure Vstar. Its diagonal construction gives terminal residual
normality, terminal-center containment, and the two normalizer calculations.
The initial and terminal normalizer theorems identify both actual quotients
with the symmetric group on four letters; the terminal theorem also gives
local self-centralization. The shared Vstar containment theorem supplies both
vertex containments.

This assembles the local witness in the final paragraph of Stellmacher (9.1),
Journal of Algebra 190 (1997), p.48. The faithful and local conclusions are
explicit hypotheses here; their upstream producers are separate results.
The preliminary containment API and Vstar re-export are preserved for callers.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven

universe u

public theorem distance_one_subgroup_le_vertex_normalizers
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1) (U : Subgroup G)
    (hU : U ≤ conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')) :
    U ≤ GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.normalizer (U : Set G) ∧
      U ≤ GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.normalizer (U : Set G) := by
  have hedge := hU.trans (distance_one_vstar_containments ctx hlength).2.2.2
  exact ⟨le_inf (hedge.trans inf_le_left) U.le_normalizer,
    le_inf (hedge.trans inf_le_right) U.le_normalizer⟩

public theorem distance_one_local_eight_normalizers
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext) :
    let V := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    ∃ U : Subgroup G, U ≤ V ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 8 ∧
      ZAt ctx.Γ ctx.criticalPath.a' ≤ U ∧ NormalIn U (EAt ctx.Γ ctx.criticalPath.a') ∧
      U ≤ GAt ctx.Γ ctx.criticalPath.a ∧ U ≤ GAt ctx.Γ ctx.criticalPath.a' ∧
      QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.normalizer (U : Set G))
        U (Equiv.Perm (Fin 4)) ∧
      QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.normalizer (U : Set G))
        U (Equiv.Perm (Fin 4)) ∧
      GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.centralizer (U : Set G) = U := by
  obtain ⟨U,hUV,hElem,hUcard,hZU,hUE,hZaN,hQnot,hself⟩ :=
    distance_one_selected_eight ctx hlength hfaithful hlocal
  have hmodela := distance_one_initial_eight_normalizer ctx.toLocalContext
    hlength hfaithful hlocal U hElem hUcard hUV hZaN hQnot hself
  obtain ⟨hmodeld,hselfd⟩ := distance_one_terminal_eight_normalizer ctx
    hlength hfaithful hlocal U hElem hUcard hUV hZU hUE hZaN hQnot hself
  have hvertices := hUV.trans (distance_one_vstar_containments ctx.toLocalContext hlength).2.2.2
  exact ⟨U,hUV,hElem,hUcard,hZU,hUE,hvertices.trans inf_le_left,
    hvertices.trans inf_le_right,hmodela,hmodeld,hselfd⟩

end Stellmacher.SectionNine
