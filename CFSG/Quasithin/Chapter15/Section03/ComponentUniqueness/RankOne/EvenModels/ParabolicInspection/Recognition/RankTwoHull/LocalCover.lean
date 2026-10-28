module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# The intrinsic coverage input for the rank-two hull

The incoming local subgroup normalizes an actual elementary four-group in the
simple component. The model-specific step places the normalizer of that group
and the chosen Sylow normalizer together in a proper subgroup. Covering just the
four-group normalizer by an arbitrary conjugate parabolic is insufficient:
the same parabolic must contain the chosen Sylow normalizer.

This module states that remaining geometric obligation and proves transport
through genuine group isomorphisms. It asserts no model satisfies it.
Source: Aschbacher--Smith, 15.3.43(e), printed p.1140, and the rank-two
catalogue in A.2.3--4, printed p.33.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

/-- Intrinsic coverage needed by the rank-two hull construction. The full
normalizers of a Sylow two-subgroup and of its invariant four-group lie in
one proper subgroup. This is a geometric conclusion to prove for each actual
model, not a hypothesis included in the reduced configuration. -/
def FourGroupNormalizerCover (K : Type*) [Group K] : Prop :=
  ∀ (P : Sylow 2 K) (R : Subgroup K), IsElementaryAbelian 2 R → Nat.card R = 4 →
    (P : Subgroup K) ≤ normalizer (R : Set K) →
      normalizer (P : Set K) ⊔ normalizer (R : Set K) < ⊤

/-- Transport coverage through an actual model isomorphism. -/
theorem FourGroupNormalizerCover.of_mulEquiv
    {K H : Type*} [Group K] [Group H] [Finite K]
    (h : FourGroupNormalizerCover H) (e : K ≃* H) : FourGroupNormalizerCover K := by
  have hs : Function.Surjective e.toMonoidHom := e.surjective
  have hb : Function.Bijective e.toMonoidHom := e.bijective
  intro P R he hc hn
  let : IsElementaryAbelian 2 R := he
  have hn' : ((P.mapSurjective (f := e.toMonoidHom) hs) : Subgroup H) ≤
      normalizer (R.map e.toMonoidHom : Set H) := by
    rw [Sylow.coe_mapSurjective]
    exact (map_mono hn).trans (R.le_normalizer_map e.toMonoidHom)
  have hc' : Nat.card (R.map e.toMonoidHom) = 4 :=
    (Nat.card_congr (e.subgroupMap R).toEquiv).symm.trans hc
  have hh := h (P.mapSurjective (f := e.toMonoidHom) hs) (R.map e.toMonoidHom)
    (IsElementaryAbelian.map e.toMonoidHom) hc' hn'
  change normalizer (((P.mapSurjective (f := e.toMonoidHom) hs : Sylow 2 H) : Subgroup H) : Set H) ⊔
    normalizer (R.map e.toMonoidHom : Set H) < ⊤ at hh
  rw [Sylow.coe_mapSurjective,
    ← map_normalizer_eq_of_bijective (P : Subgroup K) hb,
    ← map_normalizer_eq_of_bijective R hb, ← Subgroup.map_sup,
    ← map_top_of_surjective e.toMonoidHom hs] at hh
  exact (map_lt_map_iff_of_injective hb.1).mp hh

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
