module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness.Kernel
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness.Coprime

/-!
# The layer contribution to 15.3.49(a)

Ordinary components of H/O₂(H) lift to genuine C-components of H. Thus
centralization by the two-core and by all C-components, together with the
proved coprime Fitting calculation, gives centralization by the inverse
image of F*(H/O₂(H)).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1142.
The C-component centralization premise is explicit and still requires the
empty faithful-local-family argument at the source assembly boundary.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness

/-- An ordinary component is a genuine C-component. -/
theorem isCComponent_of_isComponent {G : Type*} [Group G] [Finite G]
    {L : Subgroup G} (hL : IsComponent G L) : L.IsCComponent := by
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  refine ⟨(nontrivial_iff_ne_bot L).mp inferInstance, inferInstance, hL.1, ?_⟩
  intro K hKL hK hp hs
  let := hp
  rcases IsQuasisimple.subnormal_le_center_or_eq_top (K.subgroupOf L) hs.subgroupOf with hc | ht
  · have he : ⁅K.subgroupOf L, K.subgroupOf L⁆ = ⊥ :=
      le_bot_iff.mp ((commutator_mono hc le_top).trans
        (commutator_center_left (⊤ : Subgroup L)).le)
    have hm := congrArg (map L.subtype) he
    rw [map_commutator, map_subgroupOf_eq_of_le hKL, Subgroup.map_bot, commutator_eq_self] at hm
    exact (hK hm).elim
  · exact subgroupOf_eq_top.mp ht

/-- Centralization by the two-core and all C-components centralizes the
inverse image of the ordinary layer of the two-core quotient. -/
theorem layer_preimage_centralizes_of_cComponents
    {G : Type*} [Group G] [Finite G] (C : Subgroup G)
    (hQ : pCore 2 G ≤ centralizer (C : Set G))
    (hcomp : ∀ L : Subgroup G, L.IsCComponent → L ≤ centralizer (C : Set G)) :
    (componentLayer (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)) ≤
      centralizer (C : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let D := centralizer (C : Set G)
  let : Group.IsNilpotent (pCore 2 G) := (pCore_isPGroup (p := 2) (G := G)).isNilpotent
  have hle : componentLayer (G ⧸ pCore 2 G) ≤ D.map q := by
    apply sSup_le
    intro L hL
    obtain ⟨K, hK, rfl⟩ := (isCComponent_of_isComponent hL).exists_map_quotient_eq (pCore 2 G)
    exact map_mono (hcomp K hK)
  have hm := comap_mono (f := q) hle
  exact hm.trans (by
    rw [comap_map_eq, QuotientGroup.ker_mk']
    exact sup_le le_rfl hQ)

/-- Both factors of F*(G/O₂(G)) centralize C. The Fitting factor is proved
by coprime action; the only remaining input concerns genuine C-components. -/
theorem generalizedFitting_preimage_centralizes_of_cComponents
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (C : Subgroup G) [C.Normal] [IsMulCommutative C]
    (hC : IsPGroup 2 C) (hQ : pCore 2 G ≤ centralizer (C : Set G))
    (hZ : centralInvolutions T ≤ center G)
    (hcomp : ∀ L : Subgroup G, L.IsCComponent → L ≤ centralizer (C : Set G)) :
    (generalizedFitting (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)) ≤
      centralizer (C : Set G) := by
  rw [generalizedFitting, ← comap_sup_eq _ _ _ (QuotientGroup.mk'_surjective _)]
  exact sup_le (fitting_preimage_centralizes T C hC hQ hZ)
    (layer_preimage_centralizes_of_cComponents C hQ hcomp)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness

end
