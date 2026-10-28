module
public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.MarkedIntersection
public import Theory.GroupTheory.SelfCentralizingSubgroupCenter
public import Theory.GroupTheory.Recognition.HeldM22A10.Setup

/-!
# Recognition data from the literal source involution centralizer

The plus extraspecial core in the equality branch of Proposition 6.2.13
is self-centralizing in H and lies in the original Sylow subgroup T. Its
center has order two and is central in H. Hence Z(T) is precisely that
center. Ambient simplicity also makes H proper, so the element defining
H = C_G(z) is a nonidentity involution in Z(T).

The marked-intersection theorem supplies the actual normal elementary
sixteen in H and its symmetric-four quotient. Together these construct
Held's complete local recognition input, with the original Sylow subgroup
and the original centralizer. Neither the involution order nor cyclicity
of the Sylow center is an extra input.

The earlier natural-module reduction 6.1.27, compatible M/V quotient and
extraspecial orbit geometry remain explicit source prerequisites. Global
M22/A10 recognition and the strict-intersection branch of 6.2.19 are separate
arguments; this module does not assert either conclusion conditionally as
a replacement for its missing source proof.

Source: Aschbacher--Smith, Proposition 6.2.13, printed p.688, and
Huppert--Blackburn III, XII.1.18(b), printed p.314.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
open Source
variable {G : Type*} [Group G] [Finite G]

public theorem CoreData.intermediate_center_card
    {H : Subgroup G} (T : Subgroup G) (hTH : T ≤ H)
    (P : Subgroup H) [P.Normal] (hP : CoreData P)
    (hPT : P.map H.subtype ≤ T) : Nat.card (center T) = 2 := by
  have he := center_map_eq_of_selfCentralizing T hTH P hPT hP.selfCentralizing hP.center_le
  have hc := congrArg (fun A : Subgroup G => Nat.card A) he
  rw [card_map_of_injective T.subtype_injective,
    card_map_of_injective H.subtype_injective,
    card_map_of_injective P.subtype_injective] at hc
  obtain ⟨d⟩ := hP.plusType
  exact hc.trans d.center_card

/-- An extraspecial core with the source nontrivial quotient cannot be the
whole finite simple ambient group. -/
public theorem CoreData.overgroup_ne_top [IsSimpleGroup G]
    {H : Subgroup G} (P : Subgroup H) [P.Normal] (hP : CoreData P) : H ≠ ⊤ := by
  intro hH
  let : IsSimpleGroup H := ((MulEquiv.subgroupCongr hH).trans topEquiv).isSimpleGroup
  obtain ⟨d⟩ := hP.plusType
  have hc := d.card
  rcases (inferInstance : P.Normal).eq_bot_or_eq_top with hb | ht
  · rw [hb, card_bot] at hc
    omega
  · rw [ht, card_top, hP.card] at hc
    omega

/-- The element defining the source involution centralizer is automatically
its nonidentity central involution, using the actual extraspecial geometry. -/
public theorem CoreData.centralizer_element [IsSimpleGroup G]
    {H : Subgroup G} (T : Subgroup G) (hTH : T ≤ H)
    (P : Subgroup H) [P.Normal] (hP : CoreData P)
    (hPT : P.map H.subtype ≤ T) (z : G)
    (hH : H = centralizer ({z} : Set G)) :
    ∃ zT : center T, ((zT : T) : G) = z ∧ orderOf zT = 2 := by
  have hzH : z ∈ H := hH ▸ mem_centralizer_singleton_iff.mpr rfl
  let zH : H := ⟨z, hzH⟩
  have hzP : zH ∈ P := by
    apply hP.selfCentralizing
    intro p hp
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hH ▸ p.property)
  have hzT : z ∈ T := hPT (mem_map_of_mem H.subtype hzP)
  have hzc : (⟨z, hzT⟩ : T) ∈ center T := by
    apply mem_center_iff.mpr
    intro t
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hH ▸ hTH t.property)
  let zc : center T := ⟨⟨z, hzT⟩, hzc⟩
  refine ⟨zc, rfl, orderOf_eq_prime ?_ ?_⟩
  · have hc := pow_card_eq_one' (x := zc)
    rwa [hP.intermediate_center_card T hTH P hPT] at hc
  · intro hz
    have hz1 : z = 1 := congrArg (fun a : center T => ((a : T) : G)) hz
    apply hP.overgroup_ne_top P
    rw [hH, hz1]
    exact centralizer_eq_top_iff_subset.mpr (by simp)

/-- The original source geometry supplies the complete local recognition data,
including the previously absent cyclic Sylow-center requirement. -/
@[expose] public def source_recognition_localData
    {κ : GroupClass} {T : Sylow 2 G} {L M V₀ : Subgroup G} {n : ℕ}
    (h611 : Hypothesis611 κ T L M V₀ n)
    (h6127 : Conclusion6127 (T : Subgroup G) L M V₀ n)
    (z : center T) (hz : orderOf z = 2)
    [((layer L V₀).subgroupOf M).Normal]
    (hq : CompatibleSymmetricFiveQuotient ((layer L V₀).subgroupOf M) (L.subgroupOf M))
    (P : Subgroup (centralizer ({((z : T) : G)} : Set G))) [P.Normal]
    (hP : CoreData P)
    (ha : NaturalFourOrbit P ((ZS (T : Subgroup G) L V₀).subgroupOf
      (centralizer ({((z : T) : G)} : Set G))))
    (hZS : coreCenter P ≤ (ZS (T : Subgroup G) L V₀).subgroupOf
      (centralizer ({((z : T) : G)} : Set G)))
    (hSP : (ZS (T : Subgroup G) L V₀).subgroupOf
      (centralizer ({((z : T) : G)} : Set G)) ≤ P)
    (hPT : P.map (centralizer ({((z : T) : G)} : Set G)).subtype ≤ (T : Subgroup G))
    (hbranch : (sourceEight ((ZS (T : Subgroup G) L V₀).subgroupOf
      (centralizer ({((z : T) : G)} : Set G)))).map
        (centralizer ({((z : T) : G)} : Set G)).subtype ⊓ layer L V₀ =
          ZS (T : Subgroup G) L V₀)
    (d : G) (hdL : d ∈ L)
    (hdT : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd : orderOf d = 3) :
    Theory.GroupTheory.HeldM22A10.LocalData G := by
  let H := centralizer ({((z : T) : G)} : Set G)
  have hTH : (T : Subgroup G) ≤ H := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (fun a : T => (a : G)) (mem_center_iff.mp z.property ⟨t, ht⟩))
  obtain ⟨hn, he, hc, hquot⟩ :=
    source_centralizer_extension_of_source_geometry h611 h6127 H ((z : T) : G)
      rfl hTH hq P hP ha hZS hSP hPT hbranch d hdL hdT hd
  exact {
    sylow := T
    involution := z
    involution_order := hz
    cyclic_center := isCyclic_of_prime_card (hP.intermediate_center_card (T : Subgroup G) hTH P hPT)
    kernel := centralizer (sourceEight ((ZS (T : Subgroup G) L V₀).subgroupOf H) : Set H)
    kernel_normal := hn
    kernel_elementary := he
    kernel_card := hc
    quotientEquiv := Classical.choice hquot }

/-- With exactly the preceding marked-centralizer source inputs, both the
involution and the cyclic Sylow center are constructed, rather than assumed. -/
public theorem source_nonempty_recognition_localData
    {κ : GroupClass} {T : Sylow 2 G} {L M V₀ : Subgroup G} {n : ℕ}
    (h611 : Hypothesis611 κ T L M V₀ n)
    (h6127 : Conclusion6127 (T : Subgroup G) L M V₀ n)
    (H : Subgroup G) (z : G) (hH : H = centralizer ({z} : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    [((layer L V₀).subgroupOf M).Normal]
    (hq : CompatibleSymmetricFiveQuotient ((layer L V₀).subgroupOf M) (L.subgroupOf M))
    (P : Subgroup H) [P.Normal] (hP : CoreData P)
    (ha : NaturalFourOrbit P ((ZS (T : Subgroup G) L V₀).subgroupOf H))
    (hZS : coreCenter P ≤ (ZS (T : Subgroup G) L V₀).subgroupOf H)
    (hSP : (ZS (T : Subgroup G) L V₀).subgroupOf H ≤ P)
    (hPT : P.map H.subtype ≤ (T : Subgroup G))
    (hbranch : (sourceEight ((ZS (T : Subgroup G) L V₀).subgroupOf H)).map H.subtype ⊓
      layer L V₀ = ZS (T : Subgroup G) L V₀)
    (d : G) (hdL : d ∈ L)
    (hdT : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd : orderOf d = 3) :
    Nonempty (Theory.GroupTheory.HeldM22A10.LocalData G) := by
  let : IsSimpleGroup G := h611.simpleQTKE.simple
  obtain ⟨zT, hzT, hz2⟩ := hP.centralizer_element (T : Subgroup G) hTH P hPT z hH
  subst z
  subst H
  exact ⟨source_recognition_localData h611 h6127 zT hz2 hq P hP ha hZS hSP hPT
    hbranch d hdL hdT hd⟩

end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
