module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Definitions

/-!+# Intrinsic normalizer coverage for the Borel hull

Model geometry places the full normalizers of a Sylow two-subgroup and of a
nonidentity two-subgroup it normalizes in one proper subgroup. This interface
does not impose an order-four condition. Actual group equivalences transport it.
The self-normalizing Sylow case needs only simplicity and perfectness.

Source: the defining-characteristic parabolic step in Aschbacher--Smith,
15.3.35, printed p.1139, applied to the local data of 15.3.41.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull

/-- Simultaneous coverage for an arbitrary nonidentity two-subgroup. -/
def TwoSubgroupNormalizerCover (K : Type*) [Group K] : Prop :=
  ∀ (P : Sylow 2 K) (R : Subgroup K), R ≠ ⊥ → IsPGroup 2 R →
    (P : Subgroup K) ≤ normalizer (R : Set K) →
      normalizer (P : Set K) ⊔ normalizer (R : Set K) < ⊤

/-- Coverage transports through the supplied model isomorphism. -/
theorem TwoSubgroupNormalizerCover.of_mulEquiv
    {K H : Type*} [Group K] [Group H] [Finite K]
    (h : TwoSubgroupNormalizerCover H) (e : K ≃* H) : TwoSubgroupNormalizerCover K := by
  have hs : Function.Surjective e.toMonoidHom := e.surjective
  have hb : Function.Bijective e.toMonoidHom := e.bijective
  intro P R hR hp hn
  have hR' : R.map e.toMonoidHom ≠ ⊥ := fun hz =>
    hR ((R.map_eq_bot_iff_of_injective hb.1).mp hz)
  have hn' : ((P.mapSurjective (f := e.toMonoidHom) hs) : Subgroup H) ≤
      normalizer (R.map e.toMonoidHom : Set H) := by
    rw [Sylow.coe_mapSurjective]
    exact (map_mono hn).trans (R.le_normalizer_map e.toMonoidHom)
  have hh := h (P.mapSurjective (f := e.toMonoidHom) hs)
    (R.map e.toMonoidHom) hR' (hp.map _) hn'
  change normalizer (((P.mapSurjective (f := e.toMonoidHom) hs : Sylow 2 H) :
    Subgroup H) : Set H) ⊔ normalizer (R.map e.toMonoidHom : Set H) < ⊤ at hh
  rw [Sylow.coe_mapSurjective,
    ← map_normalizer_eq_of_bijective (P : Subgroup K) hb,
    ← map_normalizer_eq_of_bijective R hb, ← Subgroup.map_sup,
    ← map_top_of_surjective e.toMonoidHom hs] at hh
  exact (map_lt_map_iff_of_injective hb.1).mp hh

/-- Self-normalizing Sylow subgroups supply coverage in a simple perfect group. -/
theorem twoSubgroupNormalizerCover_of_self_normalizing
    {K : Type*} [Group K] [Finite K] [IsSimpleGroup K] [Group.IsPerfect K]
    (h : ∀ P : Sylow 2 K, normalizer (P : Set K) = (P : Subgroup K)) :
    TwoSubgroupNormalizerCover K := by
  intro P R hR hp hn
  rw [h P, sup_eq_right.mpr hn]
  apply lt_top_iff_ne_top.mpr
  intro he
  let : R.Normal := normalizer_eq_top_iff.mp he
  have htop : R = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal R inferInstance).resolve_left hR
  have hK : IsPGroup 2 K := hp.of_equiv
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
  let : Group.IsNilpotent K := hK.isNilpotent
  exact Group.IsPerfect.not_isSolvable K inferInstance

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull
