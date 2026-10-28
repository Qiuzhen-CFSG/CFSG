module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.AmbientLift
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The original Sylow omega-center input to the C.1.27 lift

For the actual V=⟨Ω₁Z(T)^G⟩, B.2.14 gives reducedness, elementary
abelianness and centralization of O₂(G). Relative subnormal core action
bounds the seed's action on O₂(G) by U(K). Thus the source U(K)≤V and
the actual B.1.13 quotient subgroup give a subnormal two-perfect L≥K
with U(L)≤V and F*(L)=O₂(L). All quotient maps remain literal.

The module-support input is the preceding B.6.9 application in C.1.27;
the short-group irreducibility conclusion is not assumed or asserted here.
Source: Aschbacher–Smith C.1.27, printed pp.132–133.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

private theorem local_core_commutator {H K : Subgroup G} (hKH : K ≤ H)
    (hsub : (K.subgroupOf H).IsSubnormal) (hpK : IsPPerfect 2 K)
    (hQH : pCore 2 G ≤ H) : ⁅K, pCore 2 G⁆ ≤ (blockU K).map K.subtype := by
  let B := K.subgroupOf H
  let R := (pCore 2 G).subgroupOf H
  let e : B ≃* K := subgroupOfEquivOfLe hKH
  have hpB : IsPPerfect 2 B := hpK.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hc := commutator_le_core_commutator_of_isSubnormal B R hsub hpB
    (pCore_isPGroup (p := 2) (G := G)).comap_subtype le_normalizer_of_normal
  have hh := map_mono (f := H.subtype) hc
  rw [map_commutator, map_subgroupOf_eq_of_le hKH,
    map_subgroupOf_eq_of_le hQH] at hh
  have he : H.subtype.comp B.subtype = K.subtype.comp e.toMonoidHom := rfl
  have hu : (blockU B).map e.toMonoidHom = blockU K := by
    rw [blockU, blockU, map_commutator, pCore_map_iso,
      map_top_of_surjective _ e.surjective]
  change ⁅pCore 2 G, K⁆ ≤ ((blockU B).map B.subtype).map H.subtype at hh
  rw [map_map, he, ← map_map, hu, commutator_comm] at hh
  exact hh

/-- The actual source orbit and relative local block feed the ambient lift.
Only the genuine earlier U-support and B.1.13 quotient selection remain. -/
theorem source_omega_lift (T : Sylow 2 G)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    {H K : Subgroup G} (hTH : (T : Subgroup G) ≤ H) (hKH : K ≤ H)
    (hsub : (K.subgroupOf H).IsSubnormal) (hshort : IsShort K)
    (hU : (blockU K).map K.subtype ≤
      normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (B : Subgroup (G ⧸ centralizer
      (normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G)))
    (hB : B.IsSubnormal)
    (hKB : K.map (QuotientGroup.mk' (centralizer
      (normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G))) ≤ B) :
    let V := normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)
    let L := conjugateSpanBy K (B.comap (QuotientGroup.mk' (centralizer (V : Set G))))
    K ≤ L ∧ IsPPerfect 2 L ∧ L.IsSubnormal ∧ (blockU L).map L.subtype ≤ V ∧
      generalizedFitting L = pCore 2 L := by
  dsimp only
  let V := normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)
  have hv := omegaCenter_normalClosure_reduced T hchar
  let : IsElementaryAbelian 2 V := hv.elementary
  have hc : pCore 2 G ≤ centralizer (V : Set G) :=
    le_centralizer_iff.mp hv.le_centralizer_pCore
  have hk := (local_core_commutator hKH hsub hshort.twoPerfect
    (pCore_isPGroup.le_sylow_of_normal T |>.trans hTH)).trans hU
  obtain ⟨hKL, hpL, hsL, huL⟩ := lift_subnormal_quotient_block V K
    (IsElementaryAbelian.isPGroup 2 V) hchar hshort.twoPerfect hc hk B hB hKB
  exact ⟨hKL, hpL, hsL, huL, generalizedFitting_eq_pCore_of_selfCentralizing 2
    (subnormal_core_selfCentralizing hchar _ hsL)⟩

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
