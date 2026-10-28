module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.ResidualModels.Data
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableParabolic.RankOne

/-!
# The PSL₂ branch of the larger-field residual inspection

A proper subgroup of even PSL₂ containing a Sylow two-subgroup normalizes
that Sylow: an element outside the normalizer supplies opposite root groups
and hence the entire matrix group. The supplied quotient parabolic contains
the Borel, so its upstairs intersection equals the Borel.

The actor's two-core has index three, forcing three to divide the Borel
order. The concrete order `q(q - 1)` is prime to three in odd field degree,
so the degree is even. This proves the branch without using the subsequent
normal-four-group field restriction or Borel-action exclusions.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43, printed p.1140, the paragraph beginning `Assume that n > 1`.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

omit [Finite G] in
private theorem componentSylow_eq (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = S ⊓ L) : S.subgroupOf L = P := by
  apply Subgroup.map_injective L.subtype_injective
  rw [subgroupOf_map_subtype, hP]

omit [Finite G] in
private theorem borel_subgroupOf_sylow (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = S ⊓ L) :
    (borel L S).subgroupOf L = normalizer (P : Set L) := by
  rw [borel, inf_subgroupOf_left, subgroupOf_normalizer_eq inf_le_right,
    inf_subgroupOf_right, componentSylow_eq P hP]
  rfl

/-- Proper overgroups in even PSL₂ are contained in their Sylow normalizer. -/
theorem linearTwo_intersection {n : ℕ} (hm : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (hp : QuotientParabolic c) : M ⊓ L = borel L S := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let f := e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
  obtain ⟨P, hP⟩ := component_sylow c
  let T := P.mapSurjective (f := f.toMonoidHom) f.surjective
  have hproper : (M.subgroupOf L).map f.toMonoidHom ≠ ⊤ := by
    intro ht
    apply c.component_outside
    apply subgroupOf_eq_top.mp
    apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
    rw [ht, map_top_of_surjective _ f.surjective]
  have hcontain : (T : Subgroup _) ≤ (M.subgroupOf L).map f.toMonoidHom := by
    apply map_mono
    rw [← componentSylow_eq P hP]
    exact fun _ hx => c.sylow_le_M hx
  have hnorm := Theory.SpecificGroups.SymplecticFour.SolvableParabolic.proper_sylow_overgroup
    T ((M.subgroupOf L).map f.toMonoidHom) hproper hcontain
  change (M.subgroupOf L).map f.toMonoidHom ≤
    normalizer ((P : Subgroup L).map f.toMonoidHom : Set _) at hnorm
  rw [← map_equiv_normalizer_eq] at hnorm
  have hle := (map_le_map_iff_of_injective f.injective).mp hnorm
  change M.subgroupOf L ≤ normalizer (P : Set L) at hle
  rw [← borel_subgroupOf_sylow P hP] at hle
  have hmap := map_mono (f := L.subtype) hle
  rw [subgroupOf_map_subtype, map_subgroupOf_eq_of_le
    (show borel L S ≤ L from inf_le_left)] at hmap
  exact le_antisymm hmap (borel_le_intersection c hp)

include c in
/-- The cubic index excludes the three-prime Borels in odd field degree. -/
theorem linearTwo_even {n : ℕ} (hm : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (hB : M ⊓ L = borel L S) : Even n := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨P, hP⟩ := component_sylow c
  let T := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have he : (normalizer (P : Set L)).map e.toMonoidHom = normalizer (T : Set _) :=
    map_equiv_normalizer_eq (P : Subgroup L) e
  let f : normalizer (P : Set L) ≃* Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F :=
    ((equivMapOfInjective _ e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr he)).trans
        (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv F T)
  have h3Y : 3 ∣ Nat.card Yplus := c.index ▸ (pCore 2 Yplus).index_dvd_card
  have hYB : Yplus ≤ borel L S := by
    rw [← hB]
    exact le_inf ((actor_le_local c).trans inf_le_left) c.y_le_component
  have h3B := h3Y.trans (Subgroup.card_dvd_of_le hYB)
  have hBc : Nat.card (borel L S) = Nat.card (Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe
      (show borel L S ≤ L from inf_le_left)).toEquiv,
      borel_subgroupOf_sylow P hP, Nat.card_congr f.toEquiv]
  rw [hBc] at h3B
  by_contra hn
  have ho : Odd n := Nat.not_even_iff_odd.mp hn
  exact (Nat.prime_three.coprime_iff_not_dvd.mp
    (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.borel_threePrime_of_odd F hcard ho)) h3B

/-- The complete residual-inspection conclusion in the PSL₂ branch. -/
theorem linearTwo_inspection {n : ℕ} (hm : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (hp : QuotientParabolic c) : BorelModel L n ∧
      c.toComponentAction.image M ⊓ c.toComponentAction.image L =
        borel (c.toComponentAction.image L) (c.toComponentAction.image S) := by
  have hB := linearTwo_intersection c hm hp
  exact ⟨.linearTwo (linearTwo_even c hm hB) hm,
    quotient_intersection_eq_borel_of_intersection c hB⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
