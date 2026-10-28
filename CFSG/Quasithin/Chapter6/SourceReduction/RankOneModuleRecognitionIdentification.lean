module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionEquality
public import Theory.SpecificGroups.SL2.SylowNormalizerCard

/-!
# Initial witnesses for the natural-layer identification

A Sylow normalizer in the actual SL₂(4) quotient has order twelve.
Surjectivity of the original Sylow normalizer onto it gives a divisor
three, so Cauchy's theorem constructs a cubic in the original L normalizing
T ∩ L. This removes the cubic-element input from the existing equality
recognition theorem; no complement or splitting is assumed.

The two-group fixed-point theorem also constructs a central involution in
the original Z_S. Its centralizer contains T and is proper, and its literal
normal closure of Z_S has intersection with the natural layer containing Z_S.
This supplies the two source intersection cases without choosing either one.

Source: Aschbacher--Smith, §6.2, printed pp.680--691, especially the
cubic used in 6.2.13 on p.688. The local analysis, equality geometry and
strict-intersection elimination remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- Construct the actual cubic required by the marked equality recognition. -/
theorem exists_cubic_in_layer_sylow_normalizer
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n) :
    ∃ d ∈ L, d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G) ∧ orderOf d = 3 := by
  obtain ⟨F, _, _, _, hF, e, f, hf⟩ := hnatural.2.1
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T L
    h611.sylow_normalizes_L
  let q : L →* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hq
  have hcard : Nat.card (normalizer (Q : Set (Matrix.SpecialLinearGroup (Fin 2) F))) = 12 := by
    simpa [Sylow.coe_coe, hF] using
      Matrix.SpecialLinearGroup.card_sylow_normalizer_even Q
  have hdiv : 3 ∣ Nat.card (normalizer (P : Set L)) := by
    have hmap := (normalizer (P : Set L)).card_map_dvd q
    rw [P.normalizer_map_surjective q hq] at hmap
    exact (show 3 ∣ 12 by decide).trans (hcard ▸ hmap)
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (P : Set L)) 3 hdiv
  have hm : (d.val : G) ∈ normalizer (((P : Subgroup L).map L.subtype) : Set G) :=
    (P : Subgroup L).le_normalizer_map L.subtype (mem_map.mpr ⟨d.val, d.property, rfl⟩)
  rw [hP, subgroupOf_map_subtype] at hm
  refine ⟨d.val, d.val.property, hm, ?_⟩
  simpa only [Subgroup.orderOf_coe] using hd

/-- The nontrivial T-invariant plane contains a central involution of T. -/
theorem exists_central_involution_in_ZS (h611 : Hypothesis611 κ T L M R n) :
    ∃ z ∈ ZS (T : Subgroup G) L R, orderOf z = 2 ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
  have hfix := inf_centralizer_ne_bot_of_pGroups (T : Subgroup G)
    (ZS (T : Subgroup G) L R) T.isPGroup'
    (T.isPGroup'.to_le h611.ZS_le_T) h611.sylow_normalizes_ZS h611.ZS_ne_bot
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp hfix
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  let := h611.ZS_elementary
  refine ⟨z, z.property.1,
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (z : G) z.property.1) hz1, ?_⟩
  intro t ht
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp z.property.2 t ht)

/-- The source subgroup U = ⟨Z_S^{C_G(z)}⟩, embedded in G. -/
@[expose] def sourceClosure (T L R : Subgroup G) (z : G) : Subgroup G :=
  (sourceEight ((ZS T L R).subgroupOf (centralizer ({z} : Set G)))).map
    (centralizer ({z} : Set G)).subtype

/-- The elementary layer centralizes each of its marked involutions. -/
theorem layer_le_involution_centralizer (h611 : Hypothesis611 κ T L M R n)
    {z : G} (hz : z ∈ ZS (T : Subgroup G) L R) :
    layer L R ≤ centralizer ({z} : Set G) := by
  intro v hv
  exact mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (h611.layer_centralizes_ZS hv) z hz).symm

/-- This containment gives the exhaustive equality/strict source dichotomy. -/
theorem ZS_le_sourceClosure_intersection (h611 : Hypothesis611 κ T L M R n)
    {z : G} (hz : z ∈ ZS (T : Subgroup G) L R) :
    ZS (T : Subgroup G) L R ≤ sourceClosure (T : Subgroup G) L R z ⊓ layer L R := by
  refine le_inf ?_ inf_le_left
  have hZH : ZS (T : Subgroup G) L R ≤ centralizer ({z} : Set G) :=
    inf_le_left.trans (layer_le_involution_centralizer h611 hz)
  have hm := map_mono (f := (centralizer ({z} : Set G)).subtype) (sourceEight_contains
    ((ZS (T : Subgroup G) L R).subgroupOf (centralizer ({z} : Set G))))
  rwa [map_subgroupOf_eq_of_le hZH] at hm

/-- The natural reduction excludes an ambient central involution in Z_S. -/
theorem involution_centralizer_ne_top (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    {z : G} (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2) :
    centralizer ({z} : Set G) ≠ ⊤ := by
  intro he
  have hzC : z ∈ centralizer (L : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.mp (he ▸ mem_top l)
  have hm : z ∈ (T : Subgroup G) ⊓ centralizer (L : Set G) := ⟨h611.ZS_le_T hz, hzC⟩
  rw [hnatural.2.2.1] at hm
  have hz1 : z = 1 := hm
  rw [hz1, orderOf_one] at horder
  contradiction

/-- The equality-branch recognition now constructs its cubic from the
original natural reduction. The remaining local geometry is still explicit. -/
theorem m22_of_source_geometry_without_cubic
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (H : Subgroup G) (z : G) (hH : H = centralizer ({z} : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    [((layer L R).subgroupOf M).Normal]
    (hq : CompatibleSymmetricFiveQuotient ((layer L R).subgroupOf M) (L.subgroupOf M))
    (P : Subgroup H) [P.Normal] (hP : CoreData P)
    (ha : NaturalFourOrbit P ((ZS (T : Subgroup G) L R).subgroupOf H))
    (hZS : coreCenter P ≤ (ZS (T : Subgroup G) L R).subgroupOf H)
    (hSP : (ZS (T : Subgroup G) L R).subgroupOf H ≤ P)
    (hPT : P.map H.subtype ≤ (T : Subgroup G))
    (hbranch : (sourceEight ((ZS (T : Subgroup G) L R).subgroupOf H)).map H.subtype ⊓
      layer L R = ZS (T : Subgroup G) L R) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) := by
  obtain ⟨d, hdL, hdT, hd⟩ := exists_cubic_in_layer_sylow_normalizer h611 hnatural
  exact m22_of_source_geometry h611 hnatural H z hH hTH hq P hP ha hZS hSP hPT
    hbranch d hdL hdT hd

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
