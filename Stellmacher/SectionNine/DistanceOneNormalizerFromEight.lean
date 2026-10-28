module

public import Stellmacher.SectionNine.DistanceOneAmbientEightCentralizer

/-!
# The ambient normalizer input from a selected elementary eight

Given the local elementary eight used in Stellmacher (9.1)(c), its two local
S₄ quotient models and local self-centralization imply the required ambient
normalizer data. The ambient centralizer theorem first proves C_H(U)=U.
The two distinct S₄ subgroups of the actual ambient conjugation range then
transfer along the first isomorphism theorem to N_H(U)/U. Injectivity of
this equivalence preserves their distinctness; injectivity of the graph
embedding preserves the order and elementary structure of U.

This is the ambient transfer after the local selection in the final paragraph
of Stellmacher (9.1), Journal of Algebra 190 (1997), p.48. The properties of
the local eight remain explicit inputs. Its existence from the faithful and
local structure conclusions is a separate prerequisite.
-/

namespace Stellmacher.SectionNine

open Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven

universe u

/-- Transfer the selected local eight and its two normalizers into the ambient
normalizer quotient required by the distance-one assembly. -/
public theorem distance_one_normalizer_input_of_eight
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlen : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext)
    (U : Subgroup G) (hU : U ≤ conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a'))
    (hElem : IsElementaryAbelian 2 U) (hUcard : Nat.card U = 8)
    (hZ : ZAt ctx.Γ ctx.criticalPath.a' ≤ U)
    (hNorm : NormalIn U (EAt ctx.Γ ctx.criticalPath.a'))
    (hUa : U ≤ GAt ctx.Γ ctx.criticalPath.a)
    (hUd : U ≤ GAt ctx.Γ ctx.criticalPath.a')
    (hmodela : QuotientIsModel
      (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.normalizer (U : Set G)) U
      (Equiv.Perm (Fin 4)))
    (hmodeld : QuotientIsModel
      (GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.normalizer (U : Set G)) U
      (Equiv.Perm (Fin 4)))
    (hself : GAt ctx.Γ ctx.criticalPath.a' ⊓
      Subgroup.centralizer (U : Set G) = U) :
    DistanceOneNormalizerInput embedding ctx.toLocalContext := by
  have hcentral := distance_one_ambient_eight_centralizer ctx hlen hfaithful hlocal
    U hU hElem hUcard hZ hNorm hUa hUd hmodela hmodeld hself
  have hcenterCard := distance_one_terminal_center_card ctx hlen hfaithful hlocal
    (hZ.trans hU)
  have hglobal := (embedded_orderTwoVertex_residual_subnormal ctx
    ctx.criticalPath.a' hcenterCard).1
  have hUp : IsPGroup 2 (U.map embedding) := hElem.isPGroup.map embedding
  have hC : IsPGroup 2 (Subgroup.centralizer (U.map embedding : Set H)) := by
    rw [hcentral]
    exact hUp
  obtain ⟨_, _, _, _, _, X, Y, hne, hX, hY⟩ :=
    distance_one_eight_conjugation_images ctx hlen hfaithful hlocal hglobal
      U hU hElem hUcard hZ hNorm hUa hUd hmodela hmodeld hself hC
  let W := U.map embedding
  let N := Subgroup.normalizer (W : Set H)
  have hker : W.normalizerMonoidHom.ker = W.subgroupOf N := by
    rw [Subgroup.normalizerMonoidHom_ker, hcentral]
  let equiv := ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange W.normalizerMonoidHom)).symm
  let _ : IsElementaryAbelian 2 U := hElem
  have hmapElem : IsElementaryAbelian 2 W := IsElementaryAbelian.map embedding
  refine ⟨W, Subgroup.map_mono hU, hmapElem, ?_, hcentral,
    X.map equiv.toMonoidHom, Y.map equiv.toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective ctx.embedding_injective, hUcard]
  · intro heq
    exact hne (Subgroup.map_injective equiv.injective heq)
  · obtain ⟨eX⟩ := hX
    exact ⟨(X.equivMapOfInjective equiv.toMonoidHom equiv.injective).symm.trans eX⟩
  · obtain ⟨eY⟩ := hY
    exact ⟨(Y.equivMapOfInjective equiv.toMonoidHom equiv.injective).symm.trans eY⟩

end Stellmacher.SectionNine
