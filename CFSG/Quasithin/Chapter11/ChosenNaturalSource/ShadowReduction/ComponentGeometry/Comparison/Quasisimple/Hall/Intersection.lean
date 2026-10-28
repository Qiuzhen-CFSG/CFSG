module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall

/-!
# Prime-residual intersection in the 11.4.2 Hall argument

It suffices to place the elementary p-subgroups of the actor in L, for
one odd prime p dividing q−1. The actual prime-to-p residual equalities
of 11.0.4 do this inside N_G(L), preserving the p-rank on intersection
with L. The SL₃ cubic case keeps the exact preceding cubic clause.
This avoids requiring nilpotence or existence of a Hall subgroup for
the terminal contradiction. The original action projection and central
kernels are unchanged.

The final theorem applies this to the literal chosen flag. Constructing
an actor in Kz intersect N_G(L) with rank-two action image is still the
local obligation of qt-d-1222-shadow-component-comparison. The preceding
SL₃ clause remains with qt-d-1222-natural-local-geometry and final earlier
source assembly in qt-d-1222-shadow-components.
Source: Aschbacher--Smith, 11.0.4 and 11.4.2, printed pp.760,777.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
open LocalGeometry CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

private theorem primeRank_intersection_eq_of_elementary_mem
    (Y L : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hmem : ∀ y ∈ Y, y ^ p = 1 → y ∈ L) :
    primeRank p (Y ⊓ L : Subgroup G) = primeRank p Y := by
  apply le_antisymm (primeRank_mono p inf_le_left)
  obtain ⟨A,hA,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := Y) (p := p)
  let := hA
  have hm : IsElementaryAbelian p (A.map Y.subtype) := IsElementaryAbelian.map Y.subtype
  let := hm
  have hAL : A.map Y.subtype ≤ Y ⊓ L := by
    rintro _ ⟨a,ha,rfl⟩
    refine ⟨a.property,hmem a a.property ?_⟩
    exact congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha)
  let B := (A.map Y.subtype).subgroupOf (Y ⊓ L)
  let : IsElementaryAbelian p B := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hAL).toMonoidHom (subgroupOfEquivOfLe hAL).injective
  apply IsElementaryAbelian.primeRank_ge_of_card B
  rw [Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv,
    card_map_of_injective Y.subtype_injective]
  exact hcard

/-- The source residual clauses preserve the selected odd-prime rank on
intersection with L. Elementary generators suffice, so this statement
requires neither Hall existence nor nilpotence of the actor. -/
theorem primeRank_intersection_eq_of_source
    (S : D.NonbinaryNaturalInput) (c : Coordinates D S.field)
    (Y : Subgroup G) (hYM : Y ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hd : p ∣ 2 ^ S.field.degree - 1)
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      ∀ y ∈ Y, orderOf y = 3 → y ∈ L) :
    primeRank p (Y ⊓ L : Subgroup G) = primeRank p Y := by
  have hp2 : p ≠ 2 := fun he => hp.not_two_dvd_nat (by rw [he])
  have hdsq : p ∣ (2 ^ S.field.degree) ^ 2 - 1 :=
    hd.trans (Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2)
  apply primeRank_intersection_eq_of_elementary_mem
  intro y hy hpow
  have hyM : y ∈ normalizer (L : Set G) := hYM hy
  have hprime : (⟨y,hyM⟩ : normalizer (L : Set G)) ∈
      primeToResidual p (normalizer (L : Set G)) := by
    apply mem_primeToResidual_of_pow (n := 1)
    exact Subtype.ext (by simpa using hpow)
  have hmem (he : L = (primeToResidual p (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype) : y ∈ L := by
    rw [he]
    exact mem_map_of_mem _ hprime
  cases c with
  | sl3 m =>
    by_cases hp3 : p = 3
    · subst p
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hpow) with h1 | h3
      · rw [orderOf_eq_one_iff.mp h1]
        exact L.one_mem
      · exact hcubic ⟨S.field.Carrier, inferInstance, inferInstance, S.field.card_eq,
          ⟨m.groupEquiv⟩⟩ y hy h3
    · exact hmem (Preliminary.sl3_prime_residual D S m Fact.out
        (by have := (Fact.out : p.Prime).two_le; omega) hd)
  | sp4 m => exact hmem (Preliminary.sp4_prime_residual D S m Fact.out hdsq)
  | g2 m => exact hmem (Preliminary.g2_prime_residual D S m Fact.out hdsq)

/-- A rank-two image in the actual Kz-action gives the source contradiction
as soon as its actor lies in N_G(L). Prime residuals place its elementary
subgroups in L, avoiding a separate Hall existence or nilpotence assertion. -/
theorem ofFlag_false_of_normalizer_image
    (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (Y : Subgroup G) (hYK : Y ≤ (ofFlag S f X z H).Kz)
    (hYM : Y ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hd : p ∣ 2 ^ S.field.degree - 1)
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      ∀ y ∈ Y, orderOf y = 3 → y ∈ L)
    (hr : 2 ≤ primeRank p (pointHallProjection (ofFlag S f X z H) Y hYK).range) : False := by
  have hsmall := ofFlag_intersection_primeRank_le_one S f X z H h hlinear h1132 hp
  have hrY := two_le_primeRank_of_image hp (pointHallProjection (ofFlag S f X z H) Y hYK) hr
  rw [← primeRank_intersection_eq_of_source S c Y hYM hp hd hcubic] at hrY
  have hle := primeRank_mono p (inf_le_inf_right L hYK)
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
