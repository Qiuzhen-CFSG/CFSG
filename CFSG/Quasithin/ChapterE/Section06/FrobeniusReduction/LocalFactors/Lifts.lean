module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.Basic
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Residual lifts of the E.6.24 factors

An automizer subgroup is lifted first to its full preimage in N_G(V).
We then take the two-residual of that preimage, inside the preimage itself.
For an odd-order action image this residual still maps onto the image.
The full preimage is never asserted to have odd order or to be two-perfect.

This supplies the lifts used in the second paragraph of the proof of E.6.25,
Aschbacher–Smith, combined manuscript (1 March 2004), printed p.255.
Commutation of these lifts is a separate local-group question.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors

open Subgroup

variable {G : Type*} [Group G]

/-- Full preimage of an actual automizer subgroup, realized in G. -/
def automizerPreimage (V : Subgroup G) (B : Subgroup (Automizer V)) : Subgroup G :=
  (B.comap V.normalizerMonoidHom.rangeRestrict).map (normalizer (V : Set G)).subtype

/-- The two-residual of the full preimage, with relative ambient group retained. -/
def residualLift (V : Subgroup G) (B : Subgroup (Automizer V)) : Subgroup G :=
  (pResidual 2 (automizerPreimage V B)).map (automizerPreimage V B).subtype

theorem automizerPreimage_le (V : Subgroup G) (B : Subgroup (Automizer V)) :
    automizerPreimage V B ≤ normalizer (V : Set G) := map_subtype_le _

theorem residualLift_le_preimage (V : Subgroup G) (B : Subgroup (Automizer V)) :
    residualLift V B ≤ automizerPreimage V B := map_subtype_le _

theorem residualLift_le (V : Subgroup G) (B : Subgroup (Automizer V)) :
    residualLift V B ≤ normalizer (V : Set G) :=
  (residualLift_le_preimage V B).trans (automizerPreimage_le V B)

theorem inducedAutomizer_preimage (V : Subgroup G) (B : Subgroup (Automizer V)) :
    inducedAutomizer V (automizerPreimage V B) = B := by
  unfold inducedAutomizer automizerPreimage Subgroup.subgroupOf
  rw [comap_map_eq_self_of_injective (normalizer (V : Set G)).subtype_injective,
    map_comap_eq_self_of_surjective V.normalizerMonoidHom.rangeRestrict_surjective]

variable [Finite G]

/-- Residuals of preimages are two-perfect, regardless of the kernel's order. -/
theorem residualLift_twoPerfect (V : Subgroup G) (B : Subgroup (Automizer V)) :
    IsPPerfect 2 (residualLift V B) :=
  isPPerfect_embedded_pResidual 2 (automizerPreimage V B)

private theorem odd_residual_eq_top {A : Type*} [Group A] [Finite A]
    (ho : Odd (Nat.card A)) : pResidual 2 A = ⊤ := by
  apply top_unique
  intro a _
  exact mem_pResidual_of_orderOf_coprime
    (ho.coprime_two_left.of_dvd_right (orderOf_dvd_natCard a))

/-- Taking the residual of a full preimage preserves an odd action image. -/
theorem inducedAutomizer_residualLift (V : Subgroup G) (B : Subgroup (Automizer V))
    (ho : Odd (Nat.card B)) : inducedAutomizer V (residualLift V B) = B := by
  let P := automizerPreimage V B
  let f : P →* Automizer V := V.normalizerMonoidHom.rangeRestrict.comp
    (inclusion (automizerPreimage_le V B))
  have hf : (⊤ : Subgroup P).map f = B := by
    calc
      _ = inducedAutomizer V P := by
        ext b
        constructor
        · rintro ⟨p, _, rfl⟩
          exact ⟨⟨p, automizerPreimage_le V B p.property⟩, p.property, rfl⟩
        · rintro ⟨n, hn, he⟩
          exact ⟨⟨n, hn⟩, mem_top _, he⟩
      _ = B := inducedAutomizer_preimage V B
  have hmap : (pResidual 2 P).map f = B := by
    have hr := map_embedded_pResidual 2 (⊤ : Subgroup P) f
    have ht : (pResidual 2 (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype =
        pResidual 2 P := map_pResidual 2 topEquiv
    rw [ht, hf, odd_residual_eq_top ho, ← MonoidHom.range_eq_map, range_subtype] at hr
    exact hr
  change (((pResidual 2 P).map P.subtype).subgroupOf
    (normalizer (V : Set G))).map V.normalizerMonoidHom.rangeRestrict = B
  have he : ((pResidual 2 P).map P.subtype).subgroupOf (normalizer (V : Set G)) =
      (pResidual 2 P).map (inclusion (automizerPreimage_le V B)) := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      exact ⟨y, hy, Subtype.ext he⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [he, map_map]
  exact hmap

omit [Finite G] in
/-- The E.6.11 cyclic subgroup has odd order. -/
theorem regularCyclicSection_odd {M V U X : Subgroup G}
    (hX : RegularCyclicSection M V U X) (hr : 0 < subgroupCorank V U) :
    Odd (Nat.card X) := by
  rw [hX.card_eq]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [hn, pow_succ]
  refine ⟨2 ^ n - 1, ?_⟩
  have : 0 < 2 ^ n := by positivity
  omega

/-- Every factor is odd, using the actual Frobenius model and conjugacy of factors. -/
theorem decomposition_factor_odd {A W : Type*} [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) A W} {C : Subgroup A}
    (D : Representation.RegularCyclicNormalClosure.Decomposition ρ C)
    (hC : Odd (Nat.card C)) (i : Fin D.size) : Odd (Nat.card (D.factor i)) := by
  have hd : Odd (Nat.card (D.factor D.distinguished)) := by
    rcases D.alternatives with he | ⟨_, ⟨e⟩, _⟩
    · simpa only [← he] using hC
    · rw [Nat.card_congr e.toEquiv, Frobenius21.card_model]
      decide
  obtain ⟨a, ha, _⟩ := D.transitive D.distinguished i
  have hc := Nat.card_congr ((D.factor D.distinguished).equivMapOfInjective
    (MulAut.conj a).toMonoidHom (MulAut.conj a).injective).toEquiv
  rw [ha] at hc
  exact hc ▸ hd

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
