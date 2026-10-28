module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.RankOne
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison

/-!
# The exceptional centre calculation in 15.3.27

Suppose the component is normal in `I` and its star image has centre of
order three. The preimage of this centre **inside the component** is a
proper normal subgroup of a C-component, hence solvable. It is normalized
by `I`, so solvable-invariant control puts it in `M ∩ I`.

The centre is consequently a normal Sylow three-subgroup of `(M ∩ I)*`:
the rank-one shadow bounds all its Sylow three-subgroups by order three.
The prime-to-three residual therefore maps into this centre, contradicting
`L* = [L*, Y₊*]`. This proves the centralization calculation and excludes
both even-parameter `SL₃(2ⁿ)` and the genuine quasisimple triple cover of A₆.

Normality remains an explicit prerequisite; containment `Y₊ ≤ L` is not
used. In particular no solvability of the whole star kernel is assumed.
The matrix centre formula is reused from `Matrix.SL3`, whose source and
ATLAS attribution are retained in its owning module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.27(2–3), printed p.1131 (PDF p.1148), and A.3.3(1), p.42.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics

variable {G : Type*} [Group G]

private theorem residual_le_normal_three
    {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hc : Nat.card N = 3) (hb : ∀ P : Sylow 3 H, Nat.card P ≤ 3) :
    primeToResidual 3 H ≤ N := by
  have hp : IsPGroup 3 N := IsPGroup.of_card (hc.trans (pow_one 3).symm)
  obtain ⟨P, hNP⟩ := hp.exists_le_sylow
  have he : N = (P : Subgroup H) := eq_of_le_of_card_ge hNP ((hb P).trans hc.ge)
  apply primeToResidual_le
  rw [he]
  exact Nat.prime_three.coprime_iff_not_dvd.mpr P.not_dvd_index

private theorem image_sylow_three_card_le_three [Finite G]
    (d : LocalData G) {I : Subgroup G} (h : RankOneFacts d I)
    {H : Type*} [Group H] (f : d.MI I →* H) (hf : Function.Surjective f)
    (Q : Sylow 3 H) : Nat.card Q ≤ 3 := by
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hf 3 Q
  exact (Nat.le_of_dvd (Nat.card_pos (α := P)) ((P : Subgroup (d.MI I)).card_map_dvd f)).trans
    (intersection_sylow_three_card_le_three d h P)

private theorem proper_normal_component_solvable [Finite G]
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (N : Subgroup c.L) [N.Normal] (hN : N ≠ ⊤) : Group.IsSolvable N := by
  let e := subgroupOfEquivOfLe c.le_thompson
  let K := N.comap e.toMonoidHom
  have hK : K ≠ ⊤ := by
    intro he
    apply hN
    apply (comap_injective (f := e.toMonoidHom) e.surjective)
    simpa only [comap_top] using he
  let : Group.IsSolvable K := c.component.isSolvable_of_subnormal_lt_top
    (inferInstance : K.Normal).isSubnormal hK
  have hs : Group.IsSolvable (K.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective K)
  rwa [map_comap_eq_self_of_surjective e.surjective] at hs

/-- The intrinsic centre of `L*`, embedded in the actual star quotient. -/
def componentStarCenter (d : LocalData G) (I L : Subgroup G) : Subgroup (d.Star I) :=
  (center (d.starImage I L)).map (d.starImage I L).subtype

private theorem componentStarCenter_normal
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hn : (c.L.subgroupOf I).Normal) : (componentStarCenter d I c.L).Normal := by
  have hL : (d.starImage I c.L).Normal :=
    hn.map (d.starMap I) (QuotientGroup.mk'_surjective _)
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← @normalizer_eq_top _ _ (d.starImage I c.L) hL]
  exact normalizer_le_normalizer_characteristic_image _ (center _)

/-- The centralization calculation for both exceptional covers in 15.3.27.
The solvable preimage and its containment in `M ∩ I` are proved here. -/
theorem component_star_centralizes_of_center_card_three [Finite G]
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (h : RankOneFacts d I)
    (hcontrol : SolvableInvariantControl d I)
    (hn : (c.L.subgroupOf I).Normal)
    (hc : Nat.card (center (d.starImage I c.L)) = 3) :
    d.starImage I d.Yplus ≤ centralizer (d.starImage I c.L : Set (d.Star I)) := by
  let C := componentStarCenter d I c.L
  let : C.Normal := componentStarCenter_normal d c hn
  have hCC : C ≤ centralizer (d.starImage I c.L : Set (d.Star I)) := by
    rintro _ ⟨z, hz, rfl⟩ l hl
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨l, hl⟩)
  let fL : c.L →* d.Star I := (d.starMap I).comp (inclusion (component_le c))
  have hfL : fL.range = d.starImage I c.L := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  let N := C.comap fL
  have hN : N ≠ ⊤ := by
    intro he
    have hLC : d.starImage I c.L ≤ C := by
      rw [← hfL]
      rintro _ ⟨l, rfl⟩
      exact (show l ∈ N from he ▸ mem_top l)
    have hab := le_centralizer_iff_isMulCommutative.mp (hLC.trans hCC)
    let := c.star_quasisimple.toIsPerfect
    let : Nontrivial (d.starImage I c.L) :=
      (nontrivial_iff_ne_bot _).mpr (component_star_ne_bot d c)
    exact Group.IsPerfect.not_isMulCommutative (d.starImage I c.L) hab
  let : Group.IsSolvable N := proper_normal_component_solvable d c N hN
  let X := N.map c.L.subtype
  have hXI : X ≤ I := (map_subtype_le N).trans (component_le c)
  have hIX : I ≤ normalizer (X : Set G) := by
    apply le_normalizer_iff.mpr
    rintro i hi _ ⟨l, hl, rfl⟩
    have hL := (normal_subgroupOf_iff_le_normalizer (component_le c)).mp hn
    refine mem_map.mpr ⟨⟨i * l * i⁻¹, (hL hi l).mp l.property⟩, ?_, rfl⟩
    have hconj := (inferInstance : C.Normal).conj_mem (fL l) hl ((d.starMap I) ⟨i, hi⟩)
    change (d.starMap I) ((⟨i, hi⟩ : I) * ⟨l, (component_le c) l.property⟩ *
      (⟨i, hi⟩ : I)⁻¹) ∈ C
    change (d.starMap I) ⟨i, hi⟩ * (d.starMap I) ⟨l, (component_le c) l.property⟩ *
      ((d.starMap I) ⟨i, hi⟩)⁻¹ ∈ C at hconj
    simpa only [map_mul, map_inv] using hconj
  have hXM : X ≤ d.MI I := hcontrol X hXI
    (Group.isSolvable_of_surjective (c.L.subtype.subgroupMap_surjective N))
    (hI.1.2.trans hIX)
  have hCM : C ≤ d.starImage I (d.MI I) := by
    intro z hz
    have hzL : z ∈ fL.range := hfL ▸ (map_subtype_le (center (d.starImage I c.L)) hz)
    obtain ⟨l, rfl⟩ := hzL
    exact mem_map.mpr ⟨⟨l, (component_le c) l.property⟩,
      hXM (mem_map.mpr ⟨l, hz, rfl⟩), rfl⟩
  let f : d.MI I →* d.Star I := (d.starMap I).comp (inclusion inf_le_right)
  have hf : f.range = d.starImage I (d.MI I) := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  have hCr : C ≤ f.range := hf ▸ hCM
  have hCcard : Nat.card (C.subgroupOf f.range) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCr).toEquiv]
    exact (card_map_of_injective (d.starImage I c.L).subtype_injective).trans hc
  have hres := residual_le_normal_three (C.subgroupOf f.range) hCcard
    (image_sylow_three_card_le_three d h f.rangeRestrict f.rangeRestrict_surjective)
  have hmap : (primeToResidual 3 (d.MI I)).map f.rangeRestrict ≤ C.subgroupOf f.range :=
    (map_primeToResidual_le f.rangeRestrict f.rangeRestrict_surjective).trans hres
  have hY : d.starImage I d.Yplus ≤ C := by
    rintro _ ⟨i, hi, rfl⟩
    change (i : G) ∈ d.Yplus at hi
    rw [h.residual] at hi
    obtain ⟨m, hm, hmi⟩ := hi
    have hmC : f m ∈ C := hmap (mem_map_of_mem f.rangeRestrict hm)
    have he : (⟨(m : G), m.property.2⟩ : I) = i := Subtype.ext hmi
    change (d.starMap I) (⟨(m : G), m.property.2⟩ : I) ∈ C at hmC
    rwa [he] at hmC
  exact hY.trans hCC

/-- A normal component cannot have a star centre of order three. -/
theorem component_star_center_card_ne_three [Finite G]
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (h : RankOneFacts d I)
    (hcontrol : SolvableInvariantControl d I)
    (hn : (c.L.subgroupOf I).Normal) :
    Nat.card (center (d.starImage I c.L)) ≠ 3 := by
  intro hc
  exact component_star_not_centralizing d c (le_sup_left.trans hI.1.2)
    (component_star_centralizes_of_center_card_three d hI c h hcontrol hn hc)

/-- The full `SL₃(2ⁿ)` carrier is excluded when `n` is even.
The field order and actual multiplicative equivalence are retained. -/
theorem not_even_specialLinearThree [Finite G]
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (h : RankOneFacts d I)
    (hcontrol : SolvableInvariantControl d I)
    (hn : (c.L.subgroupOf I).Normal)
    (F : Type*) [Field F] [Finite F] (n : ℕ) (hnEven : Even n)
    (hF : Nat.card F = 2 ^ n) :
    ¬ Nonempty (d.starImage I c.L ≃* SL(3, F)) := by
  rintro ⟨e⟩
  have hmod : Nat.card F % 3 = 1 := by
    rw [hF]
    obtain ⟨k, rfl⟩ := hnEven
    rw [show k + k = 2 * k by omega, pow_mul, Nat.pow_mod]
    norm_num
  have hc : Nat.card (center SL(3, F)) = 3 :=
    Matrix.SL3.card_center_eq_three_of_ne_bot F
      (fun he => ((Matrix.SL3.center_eq_bot_iff_card_mod_three F).mp he) hmod)
  apply component_star_center_card_ne_three d hI c h hcontrol hn
  exact (Nat.card_congr (centerCongr e).toEquiv).trans hc

/-- The genuine quasisimple triple cover, specified by its centre and
its actual central quotient. This excludes a disconnected family label. -/
def IsTripleCoverAlternatingSix (H : Type*) [Group H] : Prop :=
  Theory.GroupTheory.IsQuasisimple H ∧ Nat.card (center H) = 3 ∧
    Nonempty ((H ⧸ center H) ≃* alternatingGroup (Fin 6))

/-- The triple-cover exclusion of 15.3.27(3), after relative normality. -/
theorem not_tripleCoverAlternatingSix [Finite G]
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (h : RankOneFacts d I)
    (hcontrol : SolvableInvariantControl d I)
    (hn : (c.L.subgroupOf I).Normal) :
    ¬ IsTripleCoverAlternatingSix (d.starImage I c.L) :=
  fun hcover => component_star_center_card_ne_three d hI c h hcontrol hn hcover.2.1

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
