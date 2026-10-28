module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.A8Reduction.Setup
public import Theory.SpecificGroups.Alternating.TranspositionExtension
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The marked C₂ × S₈ carrier of H₀

From the actual A₈ coordinates on Ki and the specified transposition
conjugation by t, construct an embedded S₈ with image ⟨Ki,t⟩. The
involution i centralizes this image. Its cyclic subgroup has trivial
intersection with the image: an element in that intersection corresponds
to a permutation centralizing A₈, hence to the identity. Multiplication
therefore embeds C₂ × S₈ with image exactly H₀ = ⟨Ki,i,t⟩. Inverting this
map gives all three markings required by `SmallExtensionModel`.

Source: the construction of H₀ ≃ Z₂ × S₈ in Aschbacher–Smith,
Lemma 2.5.26, printed pp.568–569 of the combined 1 March 2004 manuscript.
The comparison with Ki C_S(i) and the remaining source argument belong
to the parent reduction. This construction uses only `LocalData`, with
no automorphism-lifting or additional generation hypothesis.
-/

open Subgroup
open QuaternionGroup (cyclicPowerHom cyclicPowerHom_one)

namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne.A8Reduction.LocalData

variable {G : Type*} [Group G]

/-- The supplied A₈ coordinates and marked involutions construct the actual
marked direct-product carrier of ⟨Ki,i,t⟩, without additional premises. -/
public theorem smallExtensionModel_nonempty (d : LocalData G) : Nonempty (SmallExtensionModel d) := by
  let f : alternatingGroup (Fin 8) →* G := d.Ki.subtype.comp d.modelKi.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp d.modelKi.symm.injective
  have hf_range : f.range = d.Ki := by
    ext k
    constructor
    · rintro ⟨a, rfl⟩
      exact (d.modelKi.symm a).property
    · intro hk
      refine ⟨d.modelKi ⟨k, hk⟩, ?_⟩
      simp [f]
  have ht2 : d.t ^ 2 = 1 := d.t_order ▸ pow_orderOf_eq_one d.t
  obtain ⟨F, hF, hFk, hFt⟩ :=
    Theory.SpecificGroups.Alternating.TranspositionExtension.exists_embedding (by decide : 4 ≤ 8)
      (0 : Fin 8) 1 (by decide) f hf d.t ht2 (by
        intro k
        simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          Subgroup.subtype_apply, MulEquiv.apply_symm_apply] using d.t_action (d.modelKi.symm k))
  have hFrange : F.range = d.Ki ⊔ zpowers d.t := by
    rw [Theory.SpecificGroups.Alternating.TranspositionExtension.range_eq
      (0 : Fin 8) 1 (by decide) f F d.t hFk hFt, hf_range]
  have hi2 : d.i ^ 2 = 1 := d.i_order ▸ pow_orderOf_eq_one d.i
  let j : Multiplicative (ZMod 2) →* G := cyclicPowerHom 2 d.i hi2
  have hji : j (Multiplicative.ofAdd 1) = d.i := cyclicPowerHom_one _ _ _
  have hj : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro c hc
    change ZMod 2 at c
    fin_cases c
    · rfl
    · change j (Multiplicative.ofAdd 1) = 1 at hc
      rw [hji] at hc
      have hi := d.i_order
      rw [hc, orderOf_one] at hi
      norm_num at hi
  have hjrange : j.range = zpowers d.i := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      change ZMod 2 at c
      fin_cases c
      · change j 1 ∈ zpowers d.i
        rw [map_one]
        exact one_mem _
      · change j (Multiplicative.ofAdd 1) ∈ zpowers d.i
        rw [hji]
        exact mem_zpowers _
    · exact zpowers_le.mpr ⟨Multiplicative.ofAdd 1, hji⟩
  have hti : d.t ∈ centralizer ({d.i} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hiS : d.i ∈ d.S :=
      (show d.SC ≤ d.S by rw [d.centralizer_K]; exact inf_le_left) d.i_mem
    exact (d.t_central d.i hiS).symm
  have hFcentral : F.range ≤ centralizer ({d.i} : Set G) := by
    rw [hFrange]
    exact sup_le d.Ki_le_centralizer (zpowers_le.mpr hti)
  have hcomm (c : Multiplicative (ZMod 2)) (q : Equiv.Perm (Fin 8)) :
      Commute (j c) (F q) := by
    change ZMod 2 at c
    fin_cases c
    · change Commute (j 1) (F q)
      rw [map_one]
      exact Commute.one_left _
    · change Commute (j (Multiplicative.ofAdd 1)) (F q)
      rw [hji]
      exact (mem_centralizer_singleton_iff.mp (hFcentral ⟨q, rfl⟩)).symm
  have hdisjoint : Disjoint j.range F.range := by
    rw [disjoint_iff_inf_le]
    rintro x ⟨⟨c, hc⟩, q, hq⟩
    have hqC : q ∈ centralizer (alternatingGroup (Fin 8) : Set (Equiv.Perm (Fin 8))) := by
      intro k hk
      apply hF
      rw [map_mul, map_mul, hq, ← hc]
      exact (hcomm c k).symm.eq
    rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 8 (by decide)] at hqC
    have hq1 : q = 1 := hqC
    rw [← hq, hq1, map_one]
    exact one_mem _
  let P : SymmetricExtension →* G := j.noncommCoprod F hcomm
  have hP : Function.Injective P :=
    (MonoidHom.noncommCoprod_injective j F hcomm).mpr ⟨hj, hF, hdisjoint⟩
  have hPrange : P.range = d.smallExtension := by
    rw [MonoidHom.noncommCoprod_range j F hcomm, hjrange, hFrange]
    change zpowers d.i ⊔ (d.Ki ⊔ zpowers d.t) = (d.Ki ⊔ zpowers d.i) ⊔ zpowers d.t
    ac_rfl
  let e : SymmetricExtension ≃* d.smallExtension :=
    (MonoidHom.ofInjective hP).trans (MulEquiv.subgroupCongr hPrange)
  have he (p : SymmetricExtension) : (e p : G) = j p.1 * F p.2 := rfl
  refine ⟨⟨e.symm, ?_, ?_, ?_⟩⟩
  · intro k y hy
    apply e.symm_apply_eq.mpr
    apply Subtype.ext
    rw [he, map_one, one_mul, hFk]
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.subtype_apply, MulEquiv.symm_apply_apply] using hy
  · intro y hy
    apply e.symm_apply_eq.mpr
    apply Subtype.ext
    rw [he, hji, map_one, mul_one]
    exact hy
  · intro y hy
    apply e.symm_apply_eq.mpr
    apply Subtype.ext
    rw [he, map_one, one_mul, hFt]
    exact hy

end CFSG.Quasithin.Chapter2.A6ShadowRankOne.A8Reduction.LocalData
