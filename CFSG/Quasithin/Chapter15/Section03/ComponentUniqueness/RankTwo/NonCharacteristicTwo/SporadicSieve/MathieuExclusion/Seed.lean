module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Definitions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoModel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ModelAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ShadowBounds
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The solvable rank-two seed in a marked simple component

The image of Y₊ in the actual L/O₂(L) model is solvable and has order divisible
by nine. Its normalizer contains a Sylow two-subgroup of the model. The proof
uses relative normality of L inside I, and the two-group quotient kernel.
These conclusions hold whether the full component action is inner or outer.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.36 and
15.3.41--42, printed pp.1135 and 1138.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion
variable {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
variable {I L M Y S : Subgroup G} [(L.subgroupOf I).Normal]

/-- The actual projection into the supplied simple model. -/
noncomputable def quotientMap (e : L ⧸ pCore 2 L ≃* A) : L →* A :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

/-- The image of Y₊, retaining its actual embedding in the component. -/
noncomputable def seed (e : L ⧸ pCore 2 L ≃* A) : Subgroup A :=
  (Y.subgroupOf L).map (quotientMap e)

omit [Finite G] [Finite A] in
private theorem quotientMap_ker (e : L ⧸ pCore 2 L ≃* A) :
    (quotientMap e).ker = pCore 2 L := by
  ext x
  change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
  rw [map_eq_one_iff e e.injective]
  exact QuotientGroup.eq_one_iff x

omit [Finite A] in
/-- The normalizer of the actual seed contains an ambient Sylow subgroup. -/
theorem seed_sylow (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* A) :
    ∃ P : Sylow 2 A, (P : Subgroup A) ≤ normalizer (seed (Y := Y) e : Set A) := by
  obtain ⟨T, hT⟩ := d.sylow
  obtain ⟨U, hU⟩ := T.exists_subgroupOf_eq_of_normal (L.subgroupOf I)
  let c := subgroupOfEquivOfLe d.component_le
  let P := U.mapSurjective (f := c.toMonoidHom) c.surjective
  have hPS : (P : Subgroup L) ≤ S.subgroupOf L := by
    rintro x ⟨u, hu, rfl⟩
    change (u : G) ∈ S
    rw [← hT, hU] at *
    exact ⟨u, hu, rfl⟩
  have hSN : S ≤ normalizer (Y : Set G) :=
    (le_inf d.sylow_le_M (d.join_eq ▸ le_sup_right)).trans
      (d.normalizer_eq ▸ inf_le_right)
  have hPN : (P : Subgroup L) ≤ normalizer (Y.subgroupOf L : Set L) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    exact ((hSN (hPS hx)) y).mp hy
  let Q := P.mapSurjective (f := quotientMap e)
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  exact ⟨Q, (map_mono hPN).trans (Subgroup.le_normalizer_map _)⟩

omit [Finite A] in
/-- Cubic exponent modulo the two-core makes the transported seed solvable. -/
theorem seed_solvable (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* A) : Group.IsSolvable (seed (Y := Y) e) := by
  have hp : IsPGroup 3 (Y ⧸ pCore 2 Y) :=
    isPGroup_iff_pow_pow_eq_one.mpr (fun x => ⟨1, by simpa using d.yplus_exponent x⟩)
  let := hp.isNilpotent
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable Y := (Group.isSolvable_iff_subgroup_quotient (pCore 2 Y)).mpr
    ⟨inferInstance, inferInstance⟩
  let : Group.IsSolvable (Y.subgroupOf L) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe d.yplus_le).toMonoidHom)
    (subgroupOfEquivOfLe d.yplus_le).injective
  exact Group.isSolvable_of_surjective
    (f := (quotientMap e).subgroupMap (Y.subgroupOf L))
    ((quotientMap e).subgroupMap_surjective _)

/-- A two-group kernel cannot destroy the source's three-rank two. -/
theorem seed_threeRank (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* A) : 2 ≤ primeRank 3 (seed (Y := Y) e) := by
  let f := (quotientMap e).subgroupMap (Y.subgroupOf L)
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap, quotientMap_ker]
    exact (pCore_isPGroup (p := 2) (G := L)).comap_subtype
  have hzero : primeRank 3 f.ker = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨n, hn⟩ := hk.exists_card_eq
    rw [hn]
    exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have h := primeRank_le_ker_add (p := 3) f
  rw [hzero, zero_add, primeRank_equiv 3 (subgroupOfEquivOfLe d.yplus_le),
    d.yplus_three_rank] at h
  exact h

/-- In particular the actual seed, not merely an abstract shadow, has a factor of nine. -/
theorem seed_nine_dvd (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* A) : 9 ∣ Nat.card (seed (Y := Y) e) := by
  obtain ⟨E, _, hE⟩ := exists_elementaryAbelian_card_primeRank
    (G := seed (Y := Y) e) (p := 3)
  have hdiv := E.card_subgroup_dvd_card
  rw [hE] at hdiv
  exact (Nat.pow_dvd_pow 3 (seed_threeRank d e)).trans hdiv

/-- If every automorphism of the carrier is inner, the full component quotient
is the same carrier. This discharges, rather than assumes, extension coverage. -/
noncomputable def wholeModelOfInner (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* A) (hi : Function.Surjective (MulAut.conj : A →* MulAut A)) :
    ComponentQuotient I L ≃* A := by
  have ht : componentImage I L L = ⊤ := by
    rw [← modelAction_comap_inner d e]
    have hh : MulAut.innerSubgroup A = ⊤ := MonoidHom.range_eq_top.mpr hi
    rw [hh, comap_top]
  exact ((Subgroup.topEquiv).symm.trans (MulEquiv.subgroupCongr ht.symm)).trans
    (componentModel d e)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion
