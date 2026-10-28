module

public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PCoreSurjective.Coordinates

/-!
# Short subgroups in normal power covers

A short subnormal subgroup acts on every normalized two-subgroup with its
whole commutator contained in the elementary layer U(B). This square-one
condition descends through arbitrary coordinate maps, whose individual
kernels may contain other components. If every such coordinate actor is
trivial, a two-group common kernel and two-perfection finish the exclusion.

This is the relative-subgroup reduction for the triality calculation in
Aschbacher–Smith 2.3.9(7), printed p.526, using C.1.7 and A.4.2(2).
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.TrialityCase.ShortSubgroups

open Subgroup ChapterC

variable {K T : Type*} [Group K] [Group T] [Finite K]

/-- Square-one control for every element of the coordinate commutator,
not just commutator generators. No coordinate-kernel restriction is used. -/
theorem coordinate_commutator_square (B N : Subgroup K)
    (hsub : B.IsSubnormal) (hb : IsShort B) (hBN : B ≤ N)
    (f : N →* T) {x : T}
    (hx : x ∈ ⁅(pCore 2 N).map f, (B.subgroupOf N).map f⁆) : x ^ 2 = 1 := by
  let Q := (pCore 2 N).map N.subtype
  have hNQ : N ≤ normalizer Q := by
    have hh := (pCore 2 N).le_normalizer_map N.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hc : ⁅Q, B⁆ ≤ (blockU B).map B.subtype :=
    commutator_le_core_commutator_of_isSubnormal B Q hsub hb.twoPerfect
      (pCore_isPGroup.map N.subtype) (hBN.trans hNQ)
  rw [← map_commutator] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hys : (y : K) ∈ ⁅Q, B⁆ := by
    have hy' := mem_map_of_mem N.subtype hy
    rwa [map_commutator, map_subgroupOf_eq_of_le hBN] at hy'
  obtain ⟨u, hu, he⟩ := hc hys
  have hu2 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    hb.elementary.exponent_dvd_p (⟨u, hu⟩ : blockU B)
  have hy2 : y ^ 2 = 1 := by
    apply Subtype.ext
    change (y : K) ^ 2 = 1
    rw [← he]
    exact congrArg (fun v : blockU B => ((v : B) : K)) hu2
  simpa only [map_pow, map_one] using congrArg f hy2

/-- A normal base with two-group quotient and a two-group-kernel power
cover detects every actual short subnormal subgroup of the overgroup. -/
theorem not_short_of_power_cover [Finite T] (N : Subgroup K) [N.Normal]
    (hquot : IsPGroup 2 (K ⧸ N)) (n : ℕ)
    (F : N →* (Fin n → T)) (hF : Function.Surjective F)
    (hker : IsPGroup 2 F.ker)
    (hrigid : ∀ X : Subgroup T, X.IsSubnormal → IsPPerfect 2 X →
      (∀ x ∈ ⁅pCore 2 T, X⁆, (x : T) ^ 2 = 1) → X = ⊥)
    (B : Subgroup K) (hsub : B.IsSubnormal) : ¬ IsShort B := by
  intro hb
  have hBN : B ≤ N := by
    have hzero := hb.twoPerfect.hom_eq_one_of_isPGroup hquot
      ((QuotientGroup.mk' N).comp B.subtype)
    intro b hb'
    exact (QuotientGroup.eq_one_iff b).mp (DFunLike.congr_fun hzero ⟨b, hb'⟩)
  let π : Fin n → N →* T := fun i => (Pi.evalMonoidHom (fun _ : Fin n => T) i).comp F
  have hπ (i : Fin n) : Function.Surjective (π i) := by
    intro t
    obtain ⟨y, hy⟩ := hF (fun _ => t)
    exact ⟨y, congrFun hy i⟩
  have hperfect : IsPPerfect 2 (B.subgroupOf N) :=
    hb.twoPerfect.of_surjective (subgroupOfEquivOfLe hBN).symm.toMonoidHom
      (subgroupOfEquivOfLe hBN).symm.surjective
  have himage (i : Fin n) : (B.subgroupOf N).map (π i) = ⊥ := by
    apply hrigid _ (hsub.subgroupOf.map (hπ i))
      (hperfect.of_surjective ((π i).subgroupMap (B.subgroupOf N))
        ((π i).subgroupMap_surjective (B.subgroupOf N)))
    intro x hx
    apply coordinate_commutator_square B N hsub hb hBN (π i)
    rwa [F.pCore_map_coordinate hF hker i]
  have hle : B.subgroupOf N ≤ F.ker := by
    intro b hb'
    apply MonoidHom.mem_ker.mpr
    funext i
    exact mem_bot.mp (himage i ▸ mem_map_of_mem (π i) hb')
  have htwo : IsPGroup 2 B :=
    (hker.to_le hle).of_equiv (subgroupOfEquivOfLe hBN)
  have hone := hb.twoPerfect.hom_eq_one_of_isPGroup htwo (MonoidHom.id B)
  apply hb.blockU_ne_bot
  apply eq_bot_iff.mpr
  intro b _
  exact mem_bot.mpr (DFunLike.congr_fun hone b)

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.TrialityCase.ShortSubgroups

end
