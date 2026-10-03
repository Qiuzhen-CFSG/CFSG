module

public import Stellmacher.AmbientCoreCentralizer
public import Stellmacher.SectionNine.DistanceOneTerminalCenter
public import Stellmacher.SectionNine.EmbeddedOrderTwoVertex
public import Stellmacher.SectionNine.DistanceOneEightCentralizerSylow

/-!
# Ambient self-centralization of the selected elementary eight

The terminal vertex center has order two inside the quaternion central product.
The embedded order-two-vertex theorem then puts its residual image subnormally
in its full ambient centralizer, proves characteristic two of that centralizer,
and identifies the common Sylow with the ambient Sylow. A normal elementary
eight in the residual lies in the ambient centralizer's two-core. Sylow
normalization puts this core inside the terminal stabilizer image, where the
supplied self-centralizer equality applies. The coprime centralizer criterion
therefore makes the full ambient centralizer of the eight a two-group.

The two local S₄ quotient models now supply the final Sylow argument: they
make the ambient normalizer nonsolvable, force its selected order-64 subgroup
to be Sylow, and place the centralizer inside the terminal stabilizer image.
This gives equality with the image of the eight. Injectivity of the graph
embedding suffices throughout; its image need not be the whole ambient group.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.1)(c), p.48, final
paragraph. The faithful and local conclusions and the properties of the
selected eight are explicit inputs from the preceding construction; neither
an ambient centralizer assumption nor a new context field is added.
-/

namespace Stellmacher.SectionNine

open Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven

private theorem centralizer_image_intersection
    {G H : Type*} [Group G] [Group H]
    (embedding : G →* H) (hinj : Function.Injective embedding)
    (P U : Subgroup G) :
    P.map embedding ⊓ Subgroup.centralizer (U.map embedding : Set H) =
      (P ⊓ Subgroup.centralizer (U : Set G)).map embedding := by
  ext element
  constructor
  · rintro ⟨⟨preimage, hpreimage, rfl⟩, hcentral⟩
    refine ⟨preimage, ⟨hpreimage, ?_⟩, rfl⟩
    change preimage ∈ Subgroup.centralizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro member hmember
    apply hinj
    simpa using Subgroup.mem_centralizer_iff.mp hcentral
      (embedding member) (Subgroup.mem_map_of_mem embedding hmember)
  · rintro ⟨preimage, ⟨hpreimage, hcentral⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem embedding hpreimage, ?_⟩
    change embedding preimage ∈ Subgroup.centralizer (U.map embedding : Set H)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨member, hmember, rfl⟩
    simpa using congrArg embedding (Subgroup.mem_centralizer_iff.mp hcentral member hmember)

universe u

private theorem distance_one_centralizer_isPGroup_of_ambient_data
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlen : ctx.criticalPath.length = 1)
    (U : Subgroup G) (helementary : IsElementaryAbelian 2 U)
    (hnormal : NormalIn U (EAt ctx.Γ ctx.criticalPath.a'))
    (hZU : ZAt ctx.Γ ctx.criticalPath.a' ≤ U)
    (hself : GAt ctx.Γ ctx.criticalPath.a' ⊓
      Subgroup.centralizer (U : Set G) = U)
    (hglobal : S = (S0 : Subgroup H))
    (hsub : SubnormalIn ((EAt ctx.Γ ctx.criticalPath.a').map embedding)
      (Subgroup.centralizer ((ZAt ctx.Γ ctx.criticalPath.a').map embedding : Set H)))
    (hchar : IsCharacteristicTwoType
      (Subgroup.centralizer ((ZAt ctx.Γ ctx.criticalPath.a').map embedding : Set H))) :
    IsPGroup 2 (Subgroup.centralizer (U.map embedding : Set H)) := by
  let P := (GAt ctx.Γ ctx.criticalPath.a').map embedding
  let C := Subgroup.centralizer ((ZAt ctx.Γ ctx.criticalPath.a').map embedding : Set H)
  have hfirst : ctx.criticalPath.firstStep = ctx.criticalPath.a' := by
    calc
      ctx.criticalPath.firstStep = ctx.criticalPath.path ⟨1, by omega⟩ :=
        ctx.criticalPath.path_first.symm
      _ = ctx.criticalPath.path ⟨ctx.criticalPath.length, by omega⟩ := by
        congr 1
        exact Fin.ext hlen.symm
      _ = ctx.criticalPath.a' := ctx.criticalPath.path_end
  have hSP : (S0 : Subgroup H) ≤ P := by
    rw [← hglobal, ← ctx.map_S]
    apply Subgroup.map_mono
    rw [← hfirst]
    exact ctx.criticalPath.S_le_edge_stabilizers.trans inf_le_right
  have hPC : P ≤ Subgroup.normalizer (C : Set H) := by
    have hPZ : P ≤ Subgroup.normalizer
        ((ZAt ctx.Γ ctx.criticalPath.a').map embedding : Set H) :=
      (Subgroup.map_mono (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a')).trans
        (Subgroup.le_normalizer_map embedding)
    exact hPZ.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  have hUE := Subgroup.map_mono (f := embedding) hnormal.1
  have hUnormal : ((U.map embedding).subgroupOf
      ((EAt ctx.Γ ctx.criticalPath.a').map embedding)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hUE).mpr
    exact (Subgroup.map_mono
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp hnormal.2)).trans
      (Subgroup.le_normalizer_map embedding)
  have hselfH : P ⊓ Subgroup.centralizer (U.map embedding : Set H) = U.map embedding := by
    rw [centralizer_image_intersection embedding ctx.embedding_injective, hself]
  exact centralizer_isPGroup_of_subnormal_data
    (U.map embedding) ((EAt ctx.Γ ctx.criticalPath.a').map embedding) C P S0
    hUE hUnormal (helementary.isPGroup.map embedding) hsub.1 hsub.2 hSP hPC
    (Subgroup.centralizer_le (Subgroup.map_mono hZU)) hselfH hchar


/-- The selected elementary eight is self-centralizing in the full ambient group. -/
public theorem distance_one_ambient_eight_centralizer
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
    Subgroup.centralizer (U.map embedding : Set H) = U.map embedding := by
  have hcard := distance_one_terminal_center_card ctx hlen hfaithful hlocal (hZ.trans hU)
  obtain ⟨hglobal, hsub, hchar⟩ :=
    embedded_orderTwoVertex_residual_subnormal ctx ctx.criticalPath.a' hcard
  have hC := distance_one_centralizer_isPGroup_of_ambient_data
    ctx hlen U hElem hNorm hZ hself hglobal hsub hchar
  exact distance_one_ambient_eight_centralizer_of_isPGroup
    ctx hlen hfaithful hlocal hglobal U hU hElem hUcard hZ hNorm hUa hUd
    hmodela hmodeld hself hC

end Stellmacher.SectionNine
