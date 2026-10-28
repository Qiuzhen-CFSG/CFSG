module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.OuterAction
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Centerlessness from the collapsed Borel

If B = N_{L₀}(T₀) = T₀, then the center of L₀* lies in the image of T₀.
The kernel of the star projection lies in T₀ by Sylow maximality, so this
image is still self-normalizing. The center is therefore a normal two-group.
But L₀* is normal in H/O₂(H) and has trivial two-core, forcing its center to
vanish. This applies to the whole component closure, including multiple
component orbits.

The final elementary lemma records the quotient action available before
collapse: mutual normalization of B and Y₀ gives [B,Y₀] ≤ T₀. The remaining
model analysis must use this action to establish B = T₀; it is not assumed
to follow from solvability alone.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.1144, proof of 15.3.49(k).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private lemma center_eq_bot_of_self_normalizing_image {D : Type*} [Group D]
    (f : G →* D) (hf : Function.Surjective f) (P : Subgroup G)
    (hP : IsPGroup 2 P) (hk : f.ker ≤ P)
    (hN : normalizer (P : Set G) = P) (hcore : pCore 2 D = ⊥) :
    center D = ⊥ := by
  have hn : normalizer (P.map f : Set D) = P.map f := by
    apply comap_injective hf
    rw [comap_normalizer_eq_of_surjective _ hf, comap_map_eq_self hk, hN]
  have hz : center D ≤ P.map f := (center_le_normalizer _).trans_eq hn
  exact le_bot_iff.mp ((show center D ≤ pCore 2 D from
    le_sSup ⟨inferInstance, (hP.map f).to_le hz⟩).trans_eq hcore)

/-- The normal closure image has trivial intrinsic two-core. -/
lemma closure_star_twoCore_eq_bot (H L Y0 T : Subgroup G)
    (hgen : H = reducedOvergroup L Y0 T)
    (hcomm : L = ⁅L, Y0⁆) (hTY : T ≤ normalizer (Y0 : Set G)) :
    pCore 2 (starImage H (localSpan L T)) = ⊥ := by
  have hn := closure_star_normal H L Y0 T hgen hcomm hTY
  rw [pCore_subnormal_eq_comap 2 hn.isSubnormal, pCore_quotient_pCore_eq_bot]
  exact (starImage H (localSpan L T)).subtype.ker_eq_bot
    (starImage H (localSpan L T)).subtype_injective

/-- A self-normalizing Sylow intersection makes the whole closure image centerless.
This argument does not identify the closure with a single component. -/
lemma closure_star_center_eq_bot_of_self_normalizing (H L Y0 : Subgroup G)
    (T : Sylow 2 G) (hgen : H = reducedOvergroup L Y0 T)
    (hcomm : L = ⁅L, Y0⁆) (hTY : (T : Subgroup G) ≤ normalizer (Y0 : Set G))
    (hN : localSpan L T ⊓ normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G) =
      (T : Subgroup G) ⊓ localSpan L T) :
    center (starImage H (localSpan L T)) = ⊥ := by
  let L0 := localSpan L (T : Subgroup G)
  let J := L0.subgroupOf H
  let T0 := (T : Subgroup G) ⊓ L0
  let q := QuotientGroup.mk' (pCore 2 H)
  let f := q.subgroupMap J
  let g := H.subtype.comp J.subtype
  let P := T0.comap g
  have hL0H : L0 ≤ H := hgen ▸ le_sup_left
  have hTH : (T : Subgroup G) ≤ H := hgen ▸ le_sup_right.trans le_sup_right
  have hg : g.range = L0 := by
    rw [MonoidHom.range_comp, range_subtype, map_subgroupOf_eq_of_le hL0H]
  have hT0range : T0 ≤ g.range := hg ▸ inf_le_right
  have hPN : normalizer (P : Set J) = P := by
    rw [← comap_normalizer_eq_of_le_range hT0range]
    apply le_antisymm _ (comap_mono T0.le_normalizer)
    intro x hx
    exact hN.le ⟨x.property, hx⟩
  have hP : IsPGroup 2 P :=
    (T.isPGroup'.comap_of_injective g (H.subtype_injective.comp J.subtype_injective)).to_le
      (comap_mono inf_le_left)
  have hk : f.ker ≤ P := by
    intro x hx
    have hqx : q (x : H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hc : (x : H) ∈ pCore 2 H := (QuotientGroup.eq_one_iff _).mp hqx
    exact ⟨pCore_isPGroup.le_sylow_of_normal (T.subtype hTH) hc, x.property⟩
  exact center_eq_bot_of_self_normalizing_image f (q.subgroupMap_surjective J) P hP hk hPN
    (closure_star_twoCore_eq_bot H L Y0 T hgen hcomm hTY)

omit [Finite G] in
/-- Mutual normalization makes the action trivial on the Borel modulo T₀. -/
lemma borel_commutator_le_sylow_intersection (Y T L0 B : Subgroup G)
    (hB : B ≤ L0) (hBY : B ≤ normalizer (Y : Set G))
    (hYB : Y ≤ normalizer (B : Set G))
    (hint : (Y ⊔ T) ⊓ L0 = T ⊓ L0) : ⁅B, Y⁆ ≤ T ⊓ L0 := by
  rw [← hint]
  exact le_inf ((le_normalizer_iff_commutator_le_right.mp hBY).trans le_sup_left)
    ((le_normalizer_iff_commutator_le_left.mp hYB).trans hB)


end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner
