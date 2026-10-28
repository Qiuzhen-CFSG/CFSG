module

public import FeitThompson.BGsection1.CentralizerLemmas

/-!
# Lifting centrality through the odd core

ABG Chapter II, Section 3, Proposition 1 (article pp21–22) first reduces
`H = O(H) C_H(Z(S))` to centrality of the image of the Sylow center in
`H / O(H)`. The lemma here performs this reduction for any 2-subgroup `T`.

Since the odd core has order coprime to 2, the centralizer of the image of
`T` is the image of its centralizer, by the coprime centralizer-lifting
lemma. If that image of `T` is central, its centralizer is the whole
quotient. Taking the inverse image gives the asserted supplement by the
odd core. The weak-closure argument needed to establish quotient
centrality is separate from this reduction.
-/

namespace ABG

/-- Centrality modulo the odd core supplies the centralizer supplement. -/
public theorem oddCore_sup_centralizer_eq_top_of_image_le_center
    {G : Type*} [Group G] [Finite G] (T : Subgroup G)
    (hT : IsPGroup 2 T)
    (hcentral : T.map (QuotientGroup.mk' (pPrimeCore 2 G)) ≤
      Subgroup.center (G ⧸ pPrimeCore 2 G)) :
    pPrimeCore 2 G ⊔ Subgroup.centralizer (T : Set G) = ⊤ := by
  let : Fact (IsPGroup 2 T) := ⟨hT⟩
  let q := QuotientGroup.mk' (pPrimeCore 2 G)
  have hmap : (Subgroup.centralizer (T : Set G)).map q = ⊤ := by
    rw [← centralizer_map_quotient_eq_map_centralizer 2 T (pPrimeCore 2 G)
      inferInstance (pPrimeCore_coprime_card (p := 2) (G := G))]
    exact Subgroup.centralizer_eq_top_iff_subset.mpr hcentral
  have hcomap := congrArg (Subgroup.comap q) hmap
  simpa only [Subgroup.comap_map_eq, q, QuotientGroup.ker_mk', Subgroup.comap_top,
    sup_comm] using hcomap
end ABG
