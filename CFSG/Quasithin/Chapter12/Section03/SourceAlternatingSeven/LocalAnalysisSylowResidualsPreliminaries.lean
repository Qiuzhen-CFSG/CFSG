module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowInputs
public import Theory.Representation.BinarySevenCode.PermutationAction
public import Theory.Representation.BinaryPermutation.SevenCommutant

/-!
# Actual local subgroups for the Sylow-centre residual argument

For a nonidentity element of C_{Ω₁Z(T)}(L), uniqueness places its whole
centralizer in N(L), and restriction supplies the relative C-component.
The natural A₇ module has no nonzero fixed points. Thus every element of
C_{Ω₁Z(T)}(L)e₆ is a nonidentity central involution of T; its centralizer
is two-local, has three-rank at most two, and contains C_L(e₆)^∞.

`CosetComponents` records the remaining C.2.7 enlargement exclusion and
relative normality. This module does not construct that source input or
identify a two-core quotient with its central quotient.

Source: Aschbacher--Smith, 3.3.22, printed p.597; uniqueness is 1.2.7.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}

namespace Setup.NaturalCoordinates
theorem centralizing_eq_one (E : S.NaturalCoordinates) (v : V)
    (hv : (v : G) ∈ centralizer (L : Set G)) : v = 1 := by
  have hfix : ∀ a : alternatingGroup (Fin 7),
      evenRepresentation a.val (E.coordinates v).toAdd = (E.coordinates v).toAdd := by
    intro a
    obtain ⟨l, rfl⟩ := S.projection_surjective a
    rw [← E.equivariant]
    congr 2
    apply Subtype.ext
    change (l : G) * (v : G) * (l : G)⁻¹ = v
    rw [hv l l.property, mul_inv_cancel_right]
  have hz : (E.coordinates v).toAdd = 0 := by
    apply evenWordsEquivNatural.injective
    rw [map_zero]
    apply BinaryPermutation.SevenCommutant.fixed_eq_zero
    intro a
    rw [← evenWordsEquivNatural_equivariant, hfix]
  apply E.coordinates.injective
  apply Multiplicative.toAdd.injective
  simpa only [map_one, toAdd_one] using hz
end Setup.NaturalCoordinates

namespace SylowNormalizer.Points
variable (P : Points E)

/-- The C.2.7 enlargement exclusion and relative normality, uniformly on
the actual fixed coset. Its constructor remains a source obligation. -/
structure CosetComponents : Prop where
  normalizes : ∀ c ∈ P.fixed,
    centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (P.sixGroup : Set G)
  component : ∀ c ∈ P.fixed,
    (P.sixGroup.subgroupOf (centralizer ({c * (P.six : G)} : Set G))).IsCComponent

theorem fixed_component_le {c : G} (hc : c ∈ P.fixed) :
    L ≤ centralizer ({c} : Set G) := by
  intro l hl
  exact mem_centralizer_singleton_iff.mpr (hc.2 l hl)

theorem fixed_sylow_le {c : G} (hc : c ∈ P.fixed) :
    (T : Subgroup G) ≤ centralizer ({c} : Set G) := by
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaCenterIn_iff _ _).mp hc.1).2.1 t ht)

theorem fixed_order_two {c : G} (hc : c ∈ P.fixed) (hne : c ≠ 1) :
    orderOf c = 2 :=
  orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp hc.1).2.2 hne

theorem fixed_centralizer_le
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {c : G} (hc : c ∈ P.fixed) (hne : c ≠ 1) :
    centralizer ({c} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨N, hCN, hN⟩ := Finite.exists_le_maximal
    (isTwoLocal_involution_centralizer (P.fixed_order_two hc hne))
  have he := (S.hypothesis.source_normalizer_maximal_unique structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2 N hN
      ((sup_le (P.fixed_component_le hc) (P.fixed_sylow_le hc)).trans hCN)
  exact he ▸ hCN

theorem fixed_component
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {c : G} (hc : c ∈ P.fixed) (hne : c ≠ 1) :
    (L.subgroupOf (centralizer ({c} : Set G))).IsCComponent := by
  exact (S.hypothesis.source_normalizer_component structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).subgroupOf_of_le
      (P.fixed_component_le hc) (P.fixed_centralizer_le structural hc hne)

theorem fixed_three_rank {c : G} (hc : c ∈ P.fixed) (hne : c ≠ 1) :
    primeRank 3 (centralizer ({c} : Set G)) ≤ 2 :=
  (S.hypothesis.simpleQTKE.twoLocal_sqtk
    (isTwoLocal_involution_centralizer (P.fixed_order_two hc hne))).stronglyQuasithin
      3 Nat.prime_three (by decide)

theorem six_mem_omega : (P.six : G) ∈ omegaCenterIn (T : Subgroup G) := by
  rw [mem_omegaCenterIn_iff]
  let _ := S.chosen.elementary
  exact ⟨S.chosen.le_sylow P.six.property, P.six_central,
    elemPow_eq_one_of_isElementaryAbelian _ P.six.property⟩

theorem sixGroup_le_coset_centralizer {c : G} (hc : c ∈ P.fixed) :
    P.sixGroup ≤ centralizer ({c * (P.six : G)} : Set G) := by
  have hle : P.sixGroup ≤ L ⊓ centralizer ({(P.six : G)} : Set G) :=
    map_subtype_le _
  intro x hx
  have hxc := mem_centralizer_singleton_iff.mp (P.fixed_component_le hc (hle hx).1)
  have hxs := mem_centralizer_singleton_iff.mp (hle hx).2
  exact mem_centralizer_singleton_iff.mpr
    (by rw [← mul_assoc, hxc, mul_assoc, hxs, ← mul_assoc])

theorem coset_mem_omega {c : G} (hc : c ∈ P.fixed) :
    c * (P.six : G) ∈ omegaCenterIn (T : Subgroup G) :=
  (omegaCenterIn (T : Subgroup G)).mul_mem hc.1 P.six_mem_omega

theorem six_ne_one : (P.six : G) ≠ 1 := by
  intro he
  have hv : P.six = 1 := Subtype.ext he
  have hw := P.six_weight
  rw [hv, map_one] at hw
  simp [weight] at hw

theorem coset_ne_one {c : G} (hc : c ∈ P.fixed) : c * (P.six : G) ≠ 1 := by
  intro he
  have hs : (P.six : G) = c⁻¹ := eq_inv_of_mul_eq_one_right he
  have hv : (P.six : G) ∈ centralizer (L : Set G) := by
    rw [hs]
    exact (centralizer (L : Set G)).inv_mem hc.2
  exact P.six_ne_one (congrArg Subtype.val (E.centralizing_eq_one P.six hv))

theorem coset_order_two {c : G} (hc : c ∈ P.fixed) :
    orderOf (c * (P.six : G)) = 2 :=
  orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp (P.coset_mem_omega hc)).2.2
    (P.coset_ne_one hc)

theorem coset_sylow_le {c : G} (hc : c ∈ P.fixed) :
    (T : Subgroup G) ≤ centralizer ({c * (P.six : G)} : Set G) := by
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaCenterIn_iff _ _).mp (P.coset_mem_omega hc)).2.1 t ht)

theorem coset_isTwoLocal {c : G} (hc : c ∈ P.fixed) :
    IsTwoLocal (centralizer ({c * (P.six : G)} : Set G)) :=
  isTwoLocal_involution_centralizer (P.coset_order_two hc)

theorem coset_three_rank {c : G} (hc : c ∈ P.fixed) :
    primeRank 3 (centralizer ({c * (P.six : G)} : Set G)) ≤ 2 :=
  (S.hypothesis.simpleQTKE.twoLocal_sqtk (P.coset_isTwoLocal hc)).stronglyQuasithin
      3 Nat.prime_three (by decide)

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
