module

public import Theory.GroupTheory.InvertedSquareCentralizer
public import Theory.GroupTheory.NormalizingInvolutionCentralizer
public import Theory.GroupTheory.PGroup.LargeHallInvertedRotation
public import Theory.GroupTheory.PGroup.QuaternionHallInvertedElement

/-!
# Involution centralizers in quaternion–Hall products

In a finite two-group, let a normal subgroup with cyclic center be generated
by commuting quaternion-eight and large noncyclic binary Hall factors. An
involution normalizing the Hall factor, with elementary abelian ambient
centralizer, has a centralizer of order two in that factor. If the involution
lies outside the normal subgroup, its centralizer in the group it generates
with the Hall factor has order four.

The proof constructs inverted order-four elements in both factors. Their
central squares agree because the center is cyclic. The inverted-square-root
calculation then gives a fixed tail of order two, and adjoining the outside
normalizing involution doubles its centralizer. The quaternion witness proves
factor invariance from the Hall factor's normalization; normalization of the
quaternion factor is not an extra hypothesis.

Both the witness interfaces and the intrinsic conclusions retain the actual
subgroups of H and their embeddings in P. This is the counting step in
Janko–Thompson, Math. Z. 113 (1970), §4, p.392, Case 1.
-/

open Subgroup

namespace Subgroup

/-- Inverted order-four witnesses in commuting factors, with central squares
and cyclic rotation centralizer, give a tail centralizer of order two. -/
public theorem card_inf_centralizer_eq_two_of_commuting_inverted_witnesses
    {P : Type*} [Group P] [Finite P]
    (H : Subgroup P) [IsCyclic (center H)] (B D : Subgroup H)
    (hc : D ≤ centralizer (B : Set H)) (v : P)
    [IsElementaryAbelian 2 (centralizer ({v} : Set P))]
    (hB : ∃ b : B, orderOf b = 4 ∧ (b : H) ^ 2 ∈ center H ∧
      v * ((b : H) : P) * v⁻¹ = (((b : H) : P))⁻¹)
    (hD : ∃ r : D, orderOf r = 4 ∧ (r : H) ^ 2 ∈ center H ∧
      v * ((r : H) : P) * v⁻¹ = (((r : H) : P))⁻¹ ∧
      IsCyclic (centralizer ({r} : Set D))) :
    Nat.card (D.map H.subtype ⊓ centralizer ({v} : Set P) : Subgroup P) = 2 := by
  obtain ⟨b, hb, hbZ, hbi⟩ := hB
  obtain ⟨r, hr, hrZ, hri, hcyc⟩ := hD
  let : IsCyclic (centralizer ({r} : Set D)) := hcyc
  have hs : (b : H) ^ 2 = (r : H) ^ 2 := by
    apply congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨(b : H) ^ 2, hbZ⟩ : center H))
      (y := (⟨(r : H) ^ 2, hrZ⟩ : center H)) ?_ ?_)
    · rw [← orderOf_coe, orderOf_pow, orderOf_coe, hb]
      decide
    · rw [← orderOf_coe, orderOf_pow, orderOf_coe, hr]
      decide
  let f : D →* P := H.subtype.comp D.subtype
  have h := card_inf_centralizer_eq_two_of_inverted_square_roots f
    (H.subtype_injective.comp D.subtype_injective) v ((b : H) : P) r hr
    (fun d => congrArg H.subtype (hc d.property b b.property))
    (congrArg H.subtype hs) hbi hri
  simpa only [f, MonoidHom.range_comp, range_subtype] using h

/-- Adjoining the outside normalizing involution to the tail doubles the
centralizer computed from the two inverted witnesses. -/
public theorem card_centralizer_join_eq_four_of_commuting_inverted_witnesses
    {P : Type*} [Group P] [Finite P]
    (H : Subgroup P) [IsCyclic (center H)] (B D : Subgroup H)
    (hc : D ≤ centralizer (B : Set H)) (v : P)
    (hv : orderOf v = 2) (hout : v ∉ H)
    (hn : v ∈ normalizer (D.map H.subtype : Set P))
    [IsElementaryAbelian 2 (centralizer ({v} : Set P))]
    (hB : ∃ b : B, orderOf b = 4 ∧ (b : H) ^ 2 ∈ center H ∧
      v * ((b : H) : P) * v⁻¹ = (((b : H) : P))⁻¹)
    (hD : ∃ r : D, orderOf r = 4 ∧ (r : H) ^ 2 ∈ center H ∧
      v * ((r : H) : P) * v⁻¹ = (((r : H) : P))⁻¹ ∧
      IsCyclic (centralizer ({r} : Set D))) :
    let L := D.map H.subtype ⊔ zpowers v
    let vL : L := ⟨v, mem_sup_right (mem_zpowers v)⟩
    Nat.card (centralizer ({vL} : Set L)) = 4 := by
  dsimp only
  rw [card_centralizer_sup_zpowers_of_normalizing_involution
    (D.map H.subtype) v (hv ▸ pow_orderOf_eq_one v)
    (fun h => hout (map_subtype_le D h)) hn,
    card_inf_centralizer_eq_two_of_commuting_inverted_witnesses H B D hc v hB hD]

/-- In a normal quaternion–Hall product with cyclic center, an involution
normalizing the large noncyclic Hall factor has exactly two fixed elements in
that factor when its ambient centralizer is elementary abelian.

No index assumption on H, normality assumption on B, or bound on elementary
abelian subgroup orders is needed. -/
public theorem card_inf_centralizer_eq_two_of_quaternion_large_hall
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (H : Subgroup P) [H.Normal] [IsCyclic (center H)]
    (B D : Subgroup H) [D.Normal]
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hD : IsBinaryHallFactor D)
    (hnc : ¬ IsCyclic D) (hlarge : 16 ≤ Nat.card D)
    (hc : D ≤ centralizer (B : Set H)) (hg : B ⊔ D = ⊤)
    (v : P) (hv : orderOf v = 2)
    (hn : v ∈ normalizer (D.map H.subtype : Set P))
    [IsElementaryAbelian 2 (centralizer ({v} : Set P))] :
    Nat.card (D.map H.subtype ⊓ centralizer ({v} : Set P) : Subgroup P) = 2 := by
  exact card_inf_centralizer_eq_two_of_commuting_inverted_witnesses H B D hc v
    (exists_inverted_quaternion_element_of_large_hall H B D hB hD hnc hlarge hc hg v hv hn)
    (exists_inverted_rotation_of_large_hall hP H B D hD hnc hlarge hc hg v hn)

/-- Adjoining an outside involution to the normalized large noncyclic Hall
factor in a normal quaternion–Hall product gives an involution centralizer of
order four, provided the ambient centralizer is elementary abelian.

The conclusion uses the concrete embedded Hall factor and the natural lift of
the involution to its join, so it applies directly to subgroup preimages. -/
public theorem card_centralizer_join_eq_four_of_quaternion_large_hall
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (H : Subgroup P) [H.Normal] [IsCyclic (center H)]
    (B D : Subgroup H) [D.Normal]
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hD : IsBinaryHallFactor D)
    (hnc : ¬ IsCyclic D) (hlarge : 16 ≤ Nat.card D)
    (hc : D ≤ centralizer (B : Set H)) (hg : B ⊔ D = ⊤)
    (v : P) (hv : orderOf v = 2) (hout : v ∉ H)
    (hn : v ∈ normalizer (D.map H.subtype : Set P))
    [IsElementaryAbelian 2 (centralizer ({v} : Set P))] :
    let L := D.map H.subtype ⊔ zpowers v
    let vL : L := ⟨v, mem_sup_right (mem_zpowers v)⟩
    Nat.card (centralizer ({vL} : Set L)) = 4 := by
  dsimp only
  rw [card_centralizer_sup_zpowers_of_normalizing_involution
    (D.map H.subtype) v (hv ▸ pow_orderOf_eq_one v)
    (fun h => hout (map_subtype_le D h)) hn,
    card_inf_centralizer_eq_two_of_quaternion_large_hall hP H B D hB hD hnc hlarge hc hg v hv hn]

end Subgroup
