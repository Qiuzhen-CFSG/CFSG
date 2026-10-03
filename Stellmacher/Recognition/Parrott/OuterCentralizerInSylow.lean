module

public import Stellmacher.Recognition.Parrott.SecondNormalizer
public import Stellmacher.Recognition.Parrott.OuterOmegaSixteen
public import Theory.GroupTheory.PGroup.OmegaImage

/-!
# The outer centralizer in the supplied Sylow subgroup

For any supplied second elementary data d, write T=d.sylow and H=C_G(z).
An involution y in T outside the two-core has C_H(y)≤T. Consequently the
actual ambient centralizers C_H(y) and C_T(y) agree, as do the ambient
images of their omega subgroups. No change of the supplied F or T is made.
The normalizer-movement and order-sixteen exclusion results are transported
to the actual C_T(y), ready for the remaining order-thirty-two case.

The faithful quotient H/O₂(H) is C₅⋊C₄. The image of T has order four,
so it centralizes the image of y. The preimage of the latter centralizer
is a two-group containing T and therefore equals T. The injective-image
omega lemma transports the resulting centralizer equality.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.674–675 and the first paragraph of p.676.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- The outer centralizer in H is the one in the supplied Sylow T. -/
public theorem outer_centralizer_inf_sylow
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (y : G) (hyT : y ∈ (d.sylow : Subgroup G))
    (hyJ : y ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype)
    (hy : orderOf y = 2) :
    (d.sylow : Subgroup G) ⊓ centralizer ({y} : Set G) =
      centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G) := by
  let H := centralizer ({z} : Set G)
  let yH : H := ⟨y, d.sylow_le_centralizer hyT⟩
  have hyH : orderOf yH = 2 := (Subgroup.orderOf_coe yH).symm.trans hy
  have hyHJ : yH ∉ pCore 2 H := fun hh => hyJ (mem_map_of_mem H.subtype hh)
  have hyLocal : yH ∈ (d.localSylow : Subgroup H) := by
    rw [d.sylow_map] at hyT
    obtain ⟨a, ha, hay⟩ := hyT
    have hayH : a = yH := Subtype.ext hay
    exact hayH ▸ ha
  have hle := parrott_outer_centralizer_le_sylow z h yH hyH hyHJ d.localSylow hyLocal
  apply le_antisymm
  · exact inf_le_inf_right _ d.sylow_le_centralizer
  · intro a ha
    have haP : (⟨a, ha.1⟩ : H) ∈ centralizer ({yH} : Set H) :=
      mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp ha.2))
    refine ⟨?_, ha.2⟩
    rw [d.sylow_map]
    exact mem_map_of_mem H.subtype (hle haP)

/-- The mapped omegas of C_H(y) and C_T(y) agree for the supplied T. -/
public theorem outer_centralizer_omega_eq
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (y : G) (hyT : y ∈ (d.sylow : Subgroup G))
    (hyJ : y ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype)
    (hy : orderOf y = 2) :
    let H := centralizer ({z} : Set G)
    let T : Subgroup G := d.sylow
    let yH : H := ⟨y, d.sylow_le_centralizer hyT⟩
    let yT : T := ⟨y, hyT⟩
    let P := centralizer ({yH} : Set H)
    let Q := centralizer ({yT} : Set T)
    (omega₁ P (p := 2)).map (H.subtype.comp P.subtype) =
      (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype) := by
  let H := centralizer ({z} : Set G)
  let T : Subgroup G := d.sylow
  let yH : H := ⟨y, d.sylow_le_centralizer hyT⟩
  let yT : T := ⟨y, hyT⟩
  let P := centralizer ({yH} : Set H)
  let Q := centralizer ({yT} : Set T)
  let f := H.subtype.comp P.subtype
  let g := T.subtype.comp Q.subtype
  have hf : Function.Injective f := H.subtype_injective.comp P.subtype_injective
  have hg : Function.Injective g := T.subtype_injective.comp Q.subtype_injective
  have hfrange : f.range = H ⊓ centralizer ({y} : Set G) := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨(b : H).property, mem_centralizer_singleton_iff.mpr
        (congrArg H.subtype (mem_centralizer_singleton_iff.mp b.property))⟩
    · intro ha
      exact ⟨⟨⟨a, ha.1⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp ha.2))⟩, rfl⟩
  have hgrange : g.range = T ⊓ centralizer ({y} : Set G) := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨(b : T).property, mem_centralizer_singleton_iff.mpr
        (congrArg T.subtype (mem_centralizer_singleton_iff.mp b.property))⟩
    · intro ha
      exact ⟨⟨⟨a, ha.1⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp ha.2))⟩, rfl⟩
  exact map_omega_eq_of_injective_of_range_eq f g hf hg
    (hfrange.trans ((d.outer_centralizer_inf_sylow h y hyT hyJ hy).symm.trans hgrange.symm)) 2 1

/-- Fusion moves the normalizer of the actual omega in the supplied T outside H. -/
public theorem outer_omega_normalizer_not_le_centralizer
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (y : G) (hyT : y ∈ (d.sylow : Subgroup G))
    (hyJ : y ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype)
    (hy : orderOf y = 2) (hconj : IsConj z y) :
    let T : Subgroup G := d.sylow
    let yT : T := ⟨y, hyT⟩
    let Q := centralizer ({yT} : Set T)
    let X := (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype)
    ¬ normalizer (X : Set G) ≤ centralizer ({z} : Set G) := by
  let H := centralizer ({z} : Set G)
  let yH : H := ⟨y, d.sylow_le_centralizer hyT⟩
  have hyH : orderOf yH = 2 := (Subgroup.orderOf_coe yH).symm.trans hy
  have hyHJ : yH ∉ pCore 2 H := fun hh => hyJ (mem_map_of_mem H.subtype hh)
  have hnot := parrott_outer_omega_normalizer_not_le_centralizer z h yH hyH hyHJ hconj
  have heq := d.outer_centralizer_omega_eq h y hyT hyJ hy
  dsimp only at hnot heq ⊢
  rw [← heq]
  exact hnot

/-- Core weak closure excludes order sixteen for the actual omega in the supplied T. -/
public theorem outer_omega_card_ne_sixteen_of_core_weakClosure
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z)
    (hcore : ∀ t : G, t ∈ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype → IsConj z t → t = z)
    (y : G) (hyT : y ∈ (d.sylow : Subgroup G))
    (hyJ : y ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype)
    (hy : orderOf y = 2) (hconj : IsConj z y) :
    let T : Subgroup G := d.sylow
    let yT : T := ⟨y, hyT⟩
    let Q := centralizer ({yT} : Set T)
    let X := (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype)
    Nat.card X ≠ 16 := by
  let H := centralizer ({z} : Set G)
  let yH : H := ⟨y, d.sylow_le_centralizer hyT⟩
  have hyH : orderOf yH = 2 := (Subgroup.orderOf_coe yH).symm.trans hy
  have hyHJ : yH ∉ pCore 2 H := fun hh => hyJ (mem_map_of_mem H.subtype hh)
  have hnot := parrott_outer_omega_card_ne_sixteen_of_core_weakClosure
    hN z h hcore yH hyH hyHJ hconj
  have heq := d.outer_centralizer_omega_eq h y hyT hyJ hy
  dsimp only at hnot heq ⊢
  rw [← heq]
  exact hnot

end Stellmacher.Recognition.ParrottSecondElementaryData
