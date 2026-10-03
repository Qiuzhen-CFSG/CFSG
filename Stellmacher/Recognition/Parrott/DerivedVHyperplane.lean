module

public import Stellmacher.Recognition.Parrott.DerivedLocalCenters
public import Stellmacher.Recognition.Parrott.CoreQuotientAction
public import Stellmacher.Recognition.Parrott.TwoSubgroupDerived
public import Theory.GroupAction.FourthPowerHyperplane

/-!
# The hyperplane for a derived-core involution centralizer

Put H=C_G(z), J=O₂(H), and E=J′. For v in the ambient image of E
outside ⟨z⟩, the image of C_J(v) in J/E has order eight. Indeed E is
elementary abelian of order 32 and is contained in C_J(v), which has
order 256 by the commutator pairing count.

This is the actual hyperplane used to calculate the image of the local
derived subgroup in J/E.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the first paragraph of p.677.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- The core centralizer of a noncentral derived element contains J′ and
has order 256; its image in the core abelianization has order eight. -/
public theorem parrott_derived_core_centralizer_hyperplane
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let i := H.subtype.comp J.subtype
    let E := (commutator J).map i
    ∀ v : G, v ∈ E → v ∉ zpowers z →
      let C := (centralizer ({v} : Set G)).comap i
      commutator J ≤ C ∧ Nat.card C = 256 ∧
        Nat.card (C.map (QuotientGroup.mk' (commutator J))) = 8 := by
  intro H J i E v hv hvz C
  obtain ⟨_, _, _, _, _, hElem, hDcard, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map i
  have hEC : commutator J ≤ C := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (setLike_mul_comm (mem_map_of_mem i hx) hv)
  have hCmap : C.map i = J.map H.subtype ⊓ centralizer ({v} : Set G) := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨mem_map_of_mem H.subtype c.property, hc⟩
    · rintro ⟨⟨xH, hxJ, rfl⟩, hxv⟩
      exact ⟨⟨xH, hxJ⟩, hxv, rfl⟩
  have hCcard : Nat.card C = 256 := by
    rw [← card_map_of_injective (K := C) (f := i)
      (H.subtype_injective.comp J.subtype_injective), hCmap]
    exact parrott_derived_core_centralizer_card z h v hv hvz
  refine ⟨hEC, hCcard, ?_⟩
  have hCindex : C.index = 2 := by
    have hc := C.card_mul_index
    rw [hCcard, h.core_card] at hc
    omega
  have hDindex : (commutator J).index = 16 := by
    have hc := (commutator J).card_mul_index
    rw [hDcard, h.core_card] at hc
    omega
  have hc := relIndex_mul_index hEC
  rw [hCindex, hDindex, ← QuotientGroup.ker_mk' (commutator J), relIndex_ker] at hc
  omega

/-- If the full local centralizer has order 512, its image in H/J has
order two. Its intersection with J is the core centralizer of order 256. -/
public theorem parrott_derived_local_centralizer_quotient_card
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let i := H.subtype.comp J.subtype
    let E := (commutator J).map i
    ∀ v : G, v ∈ E → v ∉ zpowers z →
      ∀ V : Subgroup G, H ⊓ centralizer ({v} : Set G) = V →
        Nat.card V = 512 →
        Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' J)) = 2 := by
  intro H J i E v hv hvz V hV hcard
  have hVH : V ≤ H := hV ▸ inf_le_left
  let K := V.subgroupOf H
  have hKcard : Nat.card K = 512 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv).trans hcard
  let C := J.subgroupOf K
  let j : C →* G := H.subtype.comp (K.subtype.comp C.subtype)
  have hj : Function.Injective j := H.subtype_injective.comp
    (K.subtype_injective.comp C.subtype_injective)
  have hrange : j.range = J.map H.subtype ⊓ centralizer ({v} : Set G) := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨mem_map_of_mem H.subtype c.property, ?_⟩
      have hc : ((c : K) : H).val ∈ V := (c : K).property
      rw [← hV] at hc
      exact hc.2
    · rintro ⟨⟨xH, hxJ, rfl⟩, hxv⟩
      have hxK : xH ∈ K := by
        change (xH : G) ∈ V
        rw [← hV]
        exact ⟨xH.property, hxv⟩
      exact ⟨⟨⟨xH, hxK⟩, hxJ⟩, rfl⟩
  have hCcard : Nat.card C = 256 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hj).toEquiv, hrange]
    exact parrott_derived_core_centralizer_card z h v hv hvz
  have hc := C.index_mul_card
  change J.relIndex K * Nat.card C = Nat.card K at hc
  rw [hCcard, hKcard] at hc
  have hindex : J.relIndex K = 2 := by omega
  calc
    Nat.card (K.map (QuotientGroup.mk' J)) = J.relIndex K := by
      rw [← relIndex_ker, QuotientGroup.ker_mk']
    _ = 2 := hindex

end Stellmacher.Recognition
