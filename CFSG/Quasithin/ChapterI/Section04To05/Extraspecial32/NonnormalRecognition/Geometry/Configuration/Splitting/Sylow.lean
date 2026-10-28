module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Endpoints
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.InvariantComplement

/-!
# Sylow splitting from the nonnormal quaternion action

The stabilizer of a quaternion factor has index at most two. An outside
involution and Q generate a subgroup of order 64 and index three in H;
if that involution preserved the factor, the factor would be H-normal.
Thus it swaps the factors in the nonnormal branch.

The invariant-complement theorem gives an invariant four-group D disjoint
from E. Adjoining the involution gives a complement of order eight in
Q<a>, of order 64. The actual normalizer has order 1344, so the embedded
Q<a> is Sylow. All complements are transported through the literal nested
subgroup inclusions required by Gaschütz's theorem.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois
J. Math. 47 (2003), the splitting step in Lemma 2.8 and its application
in 3.1, printed pp.36–37.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Nonnormality of the quaternion factors forces every outside involution to swap them. -/
public theorem factor_swap_of_outside_involution (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z) (q : QuaternionCentralProductData (Core z))
    (a : Centralizer z) (ha : a ^ 2 = 1) (hout : a ∉ Core z) :
    q.left.map (MulAut.conjNormal a).toMonoidHom = q.right := by
  let : MulAction (Centralizer z) (Subgroup (Core z)) :=
    MulAction.compHom _ (MulAut.conjNormal : Centralizer z →* MulAut (Core z))
  let L := MulAction.stabilizer (Centralizer z) q.left
  have hsmall : L.index ≤ 2 := by
    rw [MulAction.index_stabilizer]
    have hsub : MulAction.orbit (Centralizer z) q.left ⊆ {q.left, q.right} := by
      rintro R ⟨b, rfl⟩
      change q.left.map (MulAut.conjNormal b).toMonoidHom ∈ _
      exact (q.quaternion_subgroup_iff _).mp
        ⟨((MulAut.conjNormal b : MulAut (Core z)).subgroupMap q.left).symm.trans
          q.left_model.some⟩
    exact (Set.ncard_le_ncard hsub).trans (by simp [q.factors_ne])
  have hQL : Core z ≤ L := by
    have hl : q.left.Normal := by
      apply normalizer_eq_top_iff.mp
      apply top_unique
      rw [← q.span]
      exact sup_le q.left.le_normalizer
        ((show q.right ≤ centralizer (q.left : Set (Core z)) from
          fun c hc b hb => q.commute b hb c hc).trans (centralizer_le_normalizer _))
    intro x hx
    change q.left.map (MulAut.conj (⟨x, hx⟩ : Core z)).toMonoidHom = q.left
    exact normal_iff_map_conj_eq.mp hl _
  have hLne : L ≠ ⊤ := by
    intro hL
    apply hn q.left q.left_model
    apply normal_iff_map_conj_eq.mpr
    intro b
    have hb : b ∈ L := hL ▸ mem_top b
    change q.left.map (MulAut.conjNormal b).toMonoidHom = q.left at hb
    have hh := congrArg (Subgroup.map (Core z).subtype) hb
    rw [map_map]
    rw [map_map] at hh
    exact hh
  have haL : a ∉ L := by
    intro haL
    let T := Core z ⊔ zpowers a
    have hT : Nat.card T = 64 := by
      rw [card_sup_zpowers_of_normalizing_involution (Core z) a ha hout
        (by rw [normalizer_eq_top]; trivial), h.core_card]
    have hTi : T.index = 3 := by
      have he := T.card_mul_index
      rw [hT, h.centralizer_card] at he
      omega
    have hd := index_dvd_of_le (sup_le hQL (zpowers_le.mpr haL))
    change L.index ∣ T.index at hd
    rw [hTi] at hd
    have he := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd
    rcases he with he | he
    · exact hLne (index_eq_one.mp he)
    · omega
  rcases (q.quaternion_subgroup_iff _).mp
    ⟨((MulAut.conjNormal a : MulAut (Core z)).subgroupMap q.left).symm.trans
      q.left_model.some⟩ with he | he
  · exact (haL he).elim
  · exact he

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration


namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z g : G}

/-- The literal self-centralizing intersection has an invariant four-group complement in Q. -/
public theorem intersection_invariant_complement_of_swap
    (h : Hypotheses z) (d : IntersectionData z g)
    (q : QuaternionCentralProductData (coreInG z))
    (a : G) (haH : a ∈ Centralizer z) (ha : a ^ 2 = 1) (hout : a ∉ coreInG z)
    (hswap : (q.left.map (coreInG z).subtype).map (MulAut.conj a).toMonoidHom =
      q.right.map (coreInG z).subtype) :
    ∃ D : Subgroup G, D ≤ coreInG z ∧ Disjoint (coreIntersection z g) D ∧
      coreIntersection z g ⊔ D = coreInG z ∧ Nat.card D = 4 ∧
      IsElementaryAbelian 2 D ∧ a ∈ normalizer (D : Set G) := by
  let := d.elementary
  apply q.exists_invariant_complement_of_normalizing_involution
    (coreInG z) (coreIntersection z g) (coreIntersection_le z g) d.card ?_
    a ha hout ?_ (intersection_centralizer_le_normalizer d haH) hswap ?_
  · rw [h.coreInG_center_image]
    exact zpowers_le.mpr (distinguished_mem_intersection d)
  · rwa [h.normalizer_core]
  · rw [d.self_centralizing]
    exact coreIntersection_le z g

/-- The invariant complement extends to a complement in an actual Sylow subgroup of N_G(E). -/
public theorem intersection_sylow_complement_of_swap
    (h : Hypotheses z) (d : IntersectionData z g)
    (q : QuaternionCentralProductData (coreInG z))
    (a : G) (haH : a ∈ Centralizer z) (ha : a ^ 2 = 1) (hout : a ∉ coreInG z)
    (hswap : (q.left.map (coreInG z).subtype).map (MulAut.conj a).toMonoidHom =
      q.right.map (coreInG z).subtype) :
    ∃ S : Sylow 2 (normalizer (coreIntersection z g : Set G)),
      ∃ K : Subgroup S,
        IsComplement' (((coreIntersection z g).subgroupOf
          (normalizer (coreIntersection z g : Set G))).subgroupOf S) K := by
  obtain ⟨D, hDQ, hED, hgen, hDcard, _, haD⟩ :=
    intersection_invariant_complement_of_swap h d q a haH ha hout hswap
  let E := coreIntersection z g
  let Q := coreInG z
  let N := normalizer (E : Set G)
  let T := Q ⊔ zpowers a
  let C := D ⊔ zpowers a
  have haQ : a ∈ normalizer (Q : Set G) := h.normalizer_core.symm ▸ haH
  have hTcard : Nat.card T = 64 := by
    rw [card_sup_zpowers_of_normalizing_involution Q a ha hout haQ, h.coreInG_card]
  have hCcard : Nat.card C = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution D a ha (fun hx => hout (hDQ hx)) haD,
      hDcard]
  have hTN : T ≤ N := sup_le ((coreInG_le z).trans
    (intersection_centralizer_le_normalizer d))
    (zpowers_le.mpr (intersection_centralizer_le_normalizer d haH))
  have hET : E ≤ T := (coreIntersection_le z g).trans le_sup_left
  have hCT : C ≤ T := sup_le_sup hDQ le_rfl
  have hEC : Disjoint E C := by
    apply disjoint_def.mpr
    intro x hxE hxC
    have hxD : x ∈ D := (inf_sup_zpowers_of_normalizing_involution Q D hDQ a ha hout haD) ▸
      (show x ∈ Q ⊓ C from ⟨coreIntersection_le z g hxE, hxC⟩)
    exact disjoint_def.mp hED hxE hxD
  let P := T.subgroupOf N
  have hPcard : Nat.card P = 2 ^ (Nat.card N).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv, hTcard,
      intersection_normalizer_card d]
    decide +kernel
  let S : Sylow 2 N := Sylow.ofCard P hPcard
  let EN := E.subgroupOf N
  let CN := C.subgroupOf N
  have hEP : EN ≤ P := fun _ hx => hET hx
  have hCP : CN ≤ P := fun _ hx => hCT hx
  refine ⟨S, CN.subgroupOf P, isComplement'_of_card_mul_and_disjoint ?_ ?_⟩
  · change Nat.card (EN.subgroupOf P) * Nat.card (CN.subgroupOf P) = Nat.card P
    rw [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hCP).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe E.le_normalizer).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (hCT.trans hTN)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv, d.card, hCcard, hTcard]
  · apply disjoint_def.mpr
    intro x hxE hxC
    apply Subtype.ext
    apply Subtype.ext
    exact disjoint_def.mp hEC hxE hxC

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
