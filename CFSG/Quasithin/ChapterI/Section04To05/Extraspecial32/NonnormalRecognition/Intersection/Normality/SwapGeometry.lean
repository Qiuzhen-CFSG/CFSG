module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Normality.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Normality.SwapGeometry.Quaternion

/-!
# Normality of the fusion eight from the arranged swapping actor

The supplied witness gives an actual involution swapping the intrinsic
quaternion factors and inverting the chosen Sylow three-subgroup. The marked
involution s lies in the arranged intersection and is fixed by this actor,
whereas the whole intersection is not centralized. The intrinsic quaternion
calculation therefore makes the intersection invariant under every cubic.
Together with the two cores' normalization and the witness's generation of
H, this proves H-normality.

Finally, conjugation by the arranging element of H transports the conclusion
to the literal intersection for the original g. Construction of the arranged
witness remains the independent source 2.4 input; cubic invariance is proved
here and is not a field of the witness.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemmas 2.3(a), 2.4 and 2.6(1), pp.33–35.
-/

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem arranged_cubic_normalizes (h : Hypotheses z) (g : G)
    (hgQ : g*z*g⁻¹ ∈ coreInG z) (hg : g*z*g⁻¹ ≠ z)
    (w : ArrangedSwapWitness h g) :
    ∀ x ∈ (h.X : Subgroup (Centralizer z)), (x : G) ∈
      normalizer (coreIntersection z ((w.a : G)*g) : Set G) := by
  obtain ⟨haQ, ha⟩ := arranged_fusion_conditions h g hgQ hg w.a
  let k := (w.a : G)*g
  let A := coreIntersection z k
  let H := Centralizer z
  let F := A.subgroupOf H
  let E := F.subgroupOf (Core z)
  let j : Core z →* G := H.subtype.comp (Core z).subtype
  have hAH : A ≤ H := (coreIntersection_le z k).trans (coreInG_le z)
  have hFQ : F ≤ Core z := by
    rw [← coreInG_subgroupOf]
    exact comap_mono (coreIntersection_le z k)
  let : IsElementaryAbelian 2 A := coreIntersection_elementary h k ha
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hAH
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hFQ
  have hE : Nat.card E=8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hFQ).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv]
    exact coreIntersection_card h k haQ ha
  have hmap : E.map j=A := by
    rw [show j=H.subtype.comp (Core z).subtype from rfl, ← map_map,
      map_subgroupOf_eq_of_le hFQ, map_subgroupOf_eq_of_le hAH]
  let a : MulAut (Core z) := MulAut.conjNormal w.u
  have ha2 : a^2=1 := by change (MulAut.conjNormal w.u)^2=1; rw [← map_pow,w.square,map_one]
  have hmove : ∃ e ∈ E, a e ≠ e := by
    by_contra! hfix
    apply (w.intersection_action h g hgQ hg).2
    intro e he
    change e ∈ A at he
    rw [← hmap] at he
    obtain ⟨q,hq,rfl⟩ := he
    have hh := congrArg j (hfix q hq)
    change (w.u : G) * j q * (w.u : G)⁻¹ = j q at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let sH : H := ⟨k*z*k⁻¹, coreInG_le z haQ⟩
  have hsCore : sH ∈ Core z := by
    rw [← coreInG_subgroupOf]
    exact haQ
  let s : Core z := ⟨sH,hsCore⟩
  have hsE : s ∈ E := by
    change k*z*k⁻¹ ∈ coreIntersection z k
    exact ⟨haQ, mem_map_of_mem (MulAut.conj k).toMonoidHom h.involution_mem_coreInG⟩
  have hsa : a s=s := by
    apply Subtype.ext
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp
      (conjugate_core_le_centralizer k w.in_conjugate_core))
  have hsZ : s ∉ center (Core z) := by
    intro hs
    have hm : sH ∈ zpowers (distinguished z) :=
      h.core_center_image ▸ mem_map_of_mem (Core z).subtype hs
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, h.distinguished_order] at hm
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
    have hnlt := Finset.mem_range.mp hn
    interval_cases n
    · have hs1 : k*z*k⁻¹=1 := by
        have hh : sH=1 := by simpa only [pow_zero] using he.symm
        exact congrArg Subtype.val hh
      have ho : orderOf (k*z*k⁻¹)=2 := (MulAut.conj k).orderOf_eq z |>.trans h.involution
      rw [hs1,orderOf_one] at ho
      omega
    · have hh : sH=distinguished z := by simpa only [pow_one] using he.symm
      exact ha (congrArg Subtype.val hh)
  intro x hx
  by_cases hx1 : x=1
  · simp [hx1]
  have hx3 : x^3=1 := by
    have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : (h.X : Subgroup H)))
    rw [h.sylow_three_card] at hh
    exact congrArg Subtype.val hh
  have hxorder : orderOf x=3 := orderOf_eq_prime hx3 hx1
  have hXgen : zpowers x = (h.X : Subgroup H) :=
    eq_of_le_of_card_ge (zpowers_le.mpr hx) (by rw [Nat.card_zpowers,hxorder]; exact h.sylow_three_card.le)
  let b : MulAut (Core z) := MulAut.conjNormal x
  have hb3 : b^3=1 := by change (MulAut.conjNormal x)^3=1; rw [← map_pow,hx3,map_one]
  have hab : a*b*a⁻¹=b⁻¹ := by
    change MulAut.conjNormal w.u * MulAut.conjNormal x * (MulAut.conjNormal w.u)⁻¹ =
      (MulAut.conjNormal x)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, w.inverts x hx, map_inv]
  have hfixed (q : Core z) (hq : b q=q) : q ∈ center (Core z) := by
    have hqx : x*(q:H)=(q:H)*x :=
      mul_inv_eq_iff_eq_mul.mp (congrArg (Core z).subtype hq)
    have hxc : x ∈ centralizer ({(q:H)} : Set H) := mem_centralizer_singleton_iff.mpr hqx
    have hXC : (h.X : Subgroup H) ≤ centralizer ({(q:H)} : Set H) :=
      hXgen ▸ zpowers_le.mpr hxc
    have hqC : (q:H) ∈ centralizer (h.X : Set H) := by
      intro y hy
      exact mem_centralizer_singleton_iff.mp (hXC hy)
    have hline : (q:H) ∈ zpowers (distinguished z) := h.fixed ▸ ⟨q.property,hqC⟩
    rw [← h.core_center_image] at hline
    obtain ⟨v,hv,he⟩ := hline
    exact (Subtype.ext he : v=q) ▸ hv
  have hInv := SwapGeometry.eight_invariant w.factors E hE a b ha2 w.swaps
    hmove hb3 hab hfixed s hsE hsa hsZ
  have hj : j.comp b.toMonoidHom = (MulAut.conj (x:G)).toMonoidHom.comp j := rfl
  have hm := congrArg (Subgroup.map j) hInv
  rw [map_map,hj,← map_map,hmap] at hm
  exact mem_normalizer_iff_map_conj_eq.mpr hm

/-- Source 2.6(1), conditional only on the actual arranged swapping actor.
The conclusion concerns the original conjugator, before arrangement. -/
public theorem coreIntersection_normal_in_centralizer_of_arrangedSwap (h : Hypotheses z) (g : G)
    (hgQ : g*z*g⁻¹ ∈ coreInG z) (hg : g*z*g⁻¹ ≠ z)
    (w : ArrangedSwapWitness h g) :
    ((coreIntersection z g).subgroupOf (Centralizer z)).Normal := by
  obtain ⟨haQ, ha⟩ := arranged_fusion_conditions h g hgQ hg w.a
  let A := coreIntersection z ((w.a:G)*g)
  have hHN : Centralizer z ≤ normalizer (A : Set G) := by
    have hgen : Core z ⊔ (h.X : Subgroup (Centralizer z)) ⊔ zpowers w.u ≤
        (normalizer (A : Set G)).comap (Centralizer z).subtype := by
      apply sup_le (sup_le ?_ ?_) ?_
      · intro q hq
        exact core_normalizes_intersection h _ haQ ha (mem_map_of_mem (Centralizer z).subtype hq)
      · exact arranged_cubic_normalizes h g hgQ hg w
      · exact zpowers_le.mpr (w.intersection_action h g hgQ hg).1
    rw [w.generates] at hgen
    intro q hq
    exact hgen (mem_top (⟨q,hq⟩ : Centralizer z))
  have hmap := coreIntersection_map_conj h w.a.property g
  have hAmap : A.map (MulAut.conj (w.a:G)).toMonoidHom=A :=
    mem_normalizer_iff_map_conj_eq.mp (hHN w.a.property)
  have hEq : coreIntersection z g=A :=
    map_injective (MulAut.conj (w.a:G)).injective (hmap.trans hAmap.symm)
  apply (normal_subgroupOf_iff_le_normalizer
    ((coreIntersection_le z g).trans (coreInG_le z))).mpr
  rw [hEq]
  exact hHN

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
