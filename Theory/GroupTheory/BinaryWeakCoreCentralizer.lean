module
public import Theory.GroupTheory.ElementaryCommutingTwoGroup
public import Theory.GroupTheory.ElementaryCommutingStabilizer
public import Theory.GroupTheory.PGroup.IsolatedFour
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.BinaryWeakCoreIsolatedOddFusion

/-!
# Local reductions for binary centralizer transport

Let A be an elementary subgroup of order at least eight in a finite
two-subgroup S. If an elementary four-subgroup E of Q extends to an
elementary eight in S, then C_G(Q) stabilizes the commuting component of A.
In particular this holds when C_S(Q) contains an involution outside Q.

Conversely, failure of transport makes each four-subgroup of Q isolated
inside S. When Q has no normal four-group, C_S(Q) then has a unique
involution. Under the weak-rank hypothesis, enlarge the local centralizer
to a Sylow subgroup of C_G(Q). The common rank-three vertex B preserves
the component, and Sylow conjugacy then shows that C_G(Q) itself has a
unique involution. These are reductions for the binary fusion issue in the
remark following GLS2, Proposition 22.4(i)
(`refs/KGroup/GLS2/ChapterF.tex`). Isolation here is explicitly relative to
S; ambient four-group extension does not remove this remaining case.

Combining these reductions with solvable-centralizer transport closes the
residual case whenever C_G(Q) is solvable. Without that hypothesis, failed
transport in a simple group forces a proper nonsolvable involution
centralizer containing S and C_G(Q). This records the remaining obstruction;
it does not assert unrestricted simple-group transport.
-/

namespace Subgroup
open scoped IsMulCommutative

/-- A vertex fixed by the centralizer, and extended inside the specified
two-subgroup, gives centralizer transport. -/
public theorem elementaryCommutingConnected_conj_of_centralizer_of_extension
    {G : Type*} [Group G] [Finite G] (S A Q E D : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 D]
    (hA : 8 ≤ Nat.card A) (hE : 4 ≤ Nat.card E) (hD : 8 ≤ Nat.card D)
    (hAS : A ≤ S) (hEQ : E ≤ Q) (hED : E ≤ D) (hDS : D ≤ S)
    (c : G) (hc : c ∈ centralizer (Q : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom) := by
  have hAD := elementaryCommutingConnected_of_le_twoGroup S A D hS hA hD hAS hDS
  have hDE : ElementaryCommutingConnected 2 D E :=
    ElementaryCommutingAdjacent.connected ⟨inferInstance, by omega, inferInstance,
      by omega, fun d hd e he => congrArg Subtype.val
        (mul_comm (⟨e, hED he⟩ : D) ⟨d, hd⟩)⟩
  exact normalizer_le_elementaryCommutingComponentStabilizer A E inferInstance
    (by omega) (hAD.trans hDE)
    (centralizer_le_normalizer _ (centralizer_le hEQ hc))

/-- An involution in the local centralizer outside Q extends every
rank-two elementary subgroup of Q inside S. -/
public theorem elementaryCommutingConnected_conj_of_centralizer_involution
    {G : Type*} [Group G] [Finite G] (S A Q E : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hE : 4 ≤ Nat.card E)
    (hAS : A ≤ S) (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (t : G) (htS : t ∈ S) (htC : t ∈ centralizer (Q : Set G))
    (ht : t ^ 2 = 1) (htQ : t ∉ Q)
    (c : G) (hc : c ∈ centralizer (Q : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom) := by
  let D := E ⊔ zpowers t
  have htE : t ∉ E := fun h => htQ (hEQ h)
  have htCE : t ∈ centralizer (E : Set G) := centralizer_le hEQ htC
  let : IsElementaryAbelian 2 (zpowers t) := IsElementaryAbelian.zpowers_of_pow_eq_one ht
  let : IsElementaryAbelian 2 D :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr htCE)
  have hD : 8 ≤ Nat.card D := by
    rw [card_sup_zpowers_of_normalizing_involution E t ht htE
      (centralizer_le_normalizer _ htCE)]
    omega
  exact elementaryCommutingConnected_conj_of_centralizer_of_extension S A Q E D
    hS hA hE hD hAS hEQ le_sup_left
    (sup_le (hEQ.trans hQS) (zpowers_le.mpr htS)) c hc

/-- If Q has no normal elementary four-group, every elementary subgroup
of Q of order at least four has order exactly four. -/
public theorem card_eq_four_of_no_normal_four
    {G : Type*} [Group G] [Finite G] (Q E : Subgroup G)
    (hQ : IsPGroup 2 Q) [IsElementaryAbelian 2 E]
    (hE : 4 ≤ Nat.card E) (hEQ : E ≤ Q)
    (hno : ¬ ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ Q ∧ Q ≤ normalizer (F : Set G)) : Nat.card E = 4 := by
  have hsmall : Nat.card E < 8 := by
    by_contra h
    let : IsElementaryAbelian 2 (E.subgroupOf Q) := IsElementaryAbelian.subgroupOf hEQ
    obtain ⟨F, hFn, hFe, hFc⟩ := hQ.exists_normal_elementaryAbelian_four
      (E.subgroupOf Q) (by
        rw [Nat.card_congr (subgroupOfEquivOfLe hEQ).toEquiv]
        omega)
    let : F.Normal := hFn
    let : IsElementaryAbelian 2 F := hFe
    apply hno
    refine ⟨F.map Q.subtype, IsElementaryAbelian.map_subtype, ?_, map_subtype_le _, ?_⟩
    · simpa only [card_map_of_injective Q.subtype_injective] using hFc
    · simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
        using F.le_normalizer_map Q.subtype
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hklt : k < 3 := by
    by_contra hh
    have hb := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 3 ≤ k by omega)
    omega
  interval_cases k
  · change Nat.card E = 1 at hk
    omega
  · change Nat.card E = 2 at hk
    omega
  · exact hk

/-- A failed transport forces the specified four-group to be maximal
elementary inside S. -/
public theorem maximal_four_of_not_centralizer_transport
    {G : Type*} [Group G] [Finite G] (S A Q E : Subgroup G)
    (hS : IsPGroup 2 S) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hE : Nat.card E = 4) (hAS : A ≤ S) (hEQ : E ≤ Q)
    (c : G) (hc : c ∈ centralizer (Q : Set G))
    (hnot : ¬ ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom))
    (D : Subgroup G) (hDe : IsElementaryAbelian 2 D) (hDS : D ≤ S) (hED : E ≤ D) :
    D ≤ E := by
  let : IsElementaryAbelian 2 D := hDe
  have hsmall : Nat.card D < 8 := by
    by_contra h
    exact hnot (elementaryCommutingConnected_conj_of_centralizer_of_extension
      S A Q E D hS hA (by omega) (by omega) hAS hEQ hED hDS c hc)
  have hdiv := card_dvd_of_le hED
  rw [hE] at hdiv
  obtain ⟨k, hk⟩ := hdiv
  exact (eq_of_le_of_card_ge hED (by omega)).ge

/-- A failed transport makes each four-subgroup of Q an isolated vertex
of the graph inside S, not necessarily of the ambient graph. -/
public theorem isolated_four_of_not_centralizer_transport
    {G : Type*} [Group G] [Finite G] (S A Q E : Subgroup G)
    (hS : IsPGroup 2 S) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hE : Nat.card E = 4)
    (hAS : A ≤ S) (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (c : G) (hc : c ∈ centralizer (Q : Set G))
    (hnot : ¬ ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom))
    (W : Subgroup G) (hWe : IsElementaryAbelian 2 W) (hW : Nat.card W = 4)
    (hWS : W ≤ S) (hWC : W ≤ centralizer (E : Set G)) : W = E := by
  let : IsElementaryAbelian 2 W := hWe
  let : IsElementaryAbelian 2 (E ⊔ W : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hWC
  have hle := maximal_four_of_not_centralizer_transport S A Q E hS hA hE hAS hEQ
    c hc hnot (E ⊔ W) inferInstance (sup_le (hEQ.trans hQS) hWS) le_sup_left
  exact eq_of_le_of_card_ge (le_sup_right.trans hle) (by omega)

private theorem central_involutions_eq_of_no_normal_four
    {G : Type*} [Group G] (Q : Subgroup G)
    (hno : ¬ ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ Q ∧ Q ≤ normalizer (F : Set G))
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxQ : x ∈ Q) (hyQ : y ∈ Q)
    (hxC : x ∈ centralizer (Q : Set G)) (hyC : y ∈ centralizer (Q : Set G)) :
    x = y := by
  by_contra hxy
  let F := closure ({x, y} : Set G)
  let : IsKleinFour F := isKleinFour_closure_pair_of_orderOf x y hx hy hxy (hxC y hyQ).symm
  have hFQ : F ≤ Q := (closure_le _).mpr (by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> assumption)
  have hFC : F ≤ centralizer (Q : Set G) := (closure_le _).mpr (by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> assumption)
  apply hno
  refine ⟨F, ?_, IsKleinFour.card_four, hFQ,
    (le_centralizer_iff.mp hFC).trans (centralizer_le_normalizer _)⟩
  exact { toIsMulCommutative := IsKleinFour.isMulCommutative
          exponent_dvd_p := by simp }

/-- In the residual case, a failed transport forces the local centralizer
to have a unique involution. This conclusion uses neither simplicity nor
the weak-rank assumption on Q C_S(Q). -/
public theorem unique_involution_of_not_centralizer_transport
    {G : Type*} [Group G] [Finite G] (S A Q E : Subgroup G)
    (hS : IsPGroup 2 S) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hE : 4 ≤ Nat.card E)
    (hAS : A ≤ S) (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (hno : ¬ ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ Q ∧ Q ≤ normalizer (F : Set G))
    (c : G) (hc : c ∈ centralizer (Q : Set G))
    (hnot : ¬ ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom)) :
    ∃! t : (S ⊓ centralizer (Q : Set G) : Subgroup G), orderOf t = 2 := by
  have hQ : IsPGroup 2 Q := hS.to_le hQS
  have hQcard : 4 ≤ Nat.card Q := hE.trans (card_le_of_le hEQ)
  let : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Nontrivial (center Q) := hQ.center_nontrivial
  obtain ⟨n, hn, hcard⟩ := (hQ.to_subgroup (center Q)).nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center Q) 2
    (hcard.symm ▸ dvd_pow_self 2 (by omega : n ≠ 0))
  let zG : G := z
  have hzG : orderOf zG = 2 := by simpa only [zG, Subgroup.orderOf_coe] using hz
  have hzQ : zG ∈ Q := (z : Q).property
  have hzC : zG ∈ centralizer (Q : Set G) := by
    intro q hq
    exact congrArg Subtype.val (mem_center_iff.mp z.property (⟨q, hq⟩ : Q))
  refine ⟨⟨zG, mem_inf.mpr ⟨hQS hzQ, hzC⟩⟩, ?_, ?_⟩
  · dsimp only
    rw [← Subgroup.orderOf_coe]
    exact hzG
  intro t ht
  have htG : orderOf (t : G) = 2 := by simpa only [Subgroup.orderOf_coe] using ht
  have htQ : (t : G) ∈ Q := by
    by_contra hout
    exact hnot (elementaryCommutingConnected_conj_of_centralizer_involution S A Q E
      hS hA hE hAS hQS hEQ t t.property.1 t.property.2
      (by simpa only [htG] using pow_orderOf_eq_one (t : G)) hout c hc)
  apply Subtype.ext
  exact central_involutions_eq_of_no_normal_four Q hno t zG htG hzG
    htQ hzQ t.property.2 hzC

/-- The weak-rank hypothesis upgrades the unique-involution obstruction
from the local centralizer to the entire ambient centralizer. -/
public theorem unique_involution_centralizer_of_not_weak_rank_transport
    {G : Type*} [Group G] [Finite G] (S A Q E B : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hE : 4 ≤ Nat.card E) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hno : ¬ ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ Q ∧ Q ≤ normalizer (F : Set G))
    (c : G) (hc : c ∈ centralizer (Q : Set G))
    (hnot : ¬ ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom)) :
    ∃! t : centralizer (Q : Set G), orderOf t = 2 := by
  let C := centralizer (Q : Set G)
  let D := S ⊓ C
  have hQ : IsPGroup 2 Q := hS.to_le hQS
  have hD : IsPGroup 2 D := hS.to_le inf_le_left
  have hDC : D ≤ C := inf_le_right
  have hDCp : IsPGroup 2 (D.subgroupOf C) :=
    hD.of_injective (subgroupOfEquivOfLe hDC).toMonoidHom
      (subgroupOfEquivOfLe hDC).injective
  obtain ⟨T, hDT⟩ := hDCp.exists_le_sylow
  let U : Subgroup G := (T : Subgroup C).map C.subtype
  have hUC : U ≤ C := map_subtype_le _
  have hDU : D ≤ U := by
    intro d hd
    exact mem_map.mpr ⟨⟨d, hDC hd⟩, hDT hd, rfl⟩
  let R := Q ⊔ U
  have hR : IsPGroup 2 R := hQ.to_sup_of_normal_left' (T.isPGroup'.map C.subtype)
    (hUC.trans (centralizer_le_normalizer _))
  have hQR : Q ≤ R := le_sup_left
  have hBR : B ≤ R := hBweak.trans (sup_le_sup_left hDU Q)
  have hBS : B ≤ S := hBweak.trans (sup_le hQS inf_le_left)
  have hAB := elementaryCommutingConnected_of_le_twoGroup S A B hS hA hB hAS hBS
  have hBnot : ¬ ElementaryCommutingConnected 2 B (B.map (MulAut.conj c).toMonoidHom) := by
    intro h
    exact hnot (hAB.trans (h.trans (hAB.symm.map (MulAut.conj c))))
  obtain ⟨z, hz, hunique⟩ := unique_involution_of_not_centralizer_transport
    R B Q E hR hB hE hBR hQR hEQ hno c hc hBnot
  have hzG : orderOf (z : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hz
  have hzQ : (z : G) ∈ Q := by
    by_contra hout
    exact hBnot (elementaryCommutingConnected_conj_of_centralizer_involution R B Q E
      hR hB hE hBR hQR hEQ z z.property.1 z.property.2
      (by simpa only [hzG] using pow_orderOf_eq_one (z : G)) hout c hc)
  let zC : C := ⟨z, z.property.2⟩
  have hzC : orderOf zC = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hzG
  refine ⟨zC, hzC, ?_⟩
  intro t ht
  obtain ⟨u, htu⟩ := T.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using ht)
  obtain ⟨g, hg⟩ := isConj_iff.mp htu
  have hu : orderOf (u : C) = 2 := by
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq t).trans ht
  have huG : orderOf ((u : C) : G) = 2 := by
    simpa only [Subgroup.orderOf_coe] using hu
  have huR : ((u : C) : G) ∈ R :=
    (le_sup_right : U ≤ R) (mem_map.mpr ⟨u, u.property, rfl⟩)
  let uR : (R ⊓ centralizer (Q : Set G) : Subgroup G) :=
    ⟨u, mem_inf.mpr ⟨huR, (u : C).property⟩⟩
  have huRorder : orderOf uR = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact huG
  have huzG : ((u : C) : G) = (z : G) :=
    congrArg (fun w : (R ⊓ centralizer (Q : Set G) : Subgroup G) => (w : G))
      (hunique uR huRorder)
  have huz : (u : C) = zC := Subtype.ext huzG
  have hgfix : (MulAut.conj g) zC = zC := by
    apply Subtype.ext
    change (g : G) * (z : G) * (g : G)⁻¹ = z
    rw [← g.property z hzQ]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  apply (MulAut.conj g).injective
  exact hg.trans (huz.trans hgfix.symm)

/-- Residual weak-rank transport when the ambient centralizer is solvable.
The unique-involution hypothesis needed by the solvable product theorem
follows from failure of transport and is not an additional assumption. -/
public theorem elementaryCommutingConnected_conj_of_no_normal_four_of_solvable_centralizer
    {G : Type*} [Group G] [Finite G] (S A Q E B : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hE : 4 ≤ Nat.card E) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hno : ¬ ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ Q ∧ Q ≤ normalizer (F : Set G))
    (hsolv : Group.IsSolvable (centralizer (Q : Set G)))
    (c : G) (hc : c ∈ centralizer (Q : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom) := by
  by_contra hfail
  have hunique := unique_involution_centralizer_of_not_weak_rank_transport
    S A Q E B hS hA hE hB hAS hQS hEQ hBweak hno c hc hfail
  exact hfail (elementaryCommutingConnected_conj_of_solvable_centralizer_unique_involution
    S A Q B hS hA hB hAS hQS hBweak hsolv hunique c hc)

/-- Under the residual hypotheses, failure of transport forces a proper
nonsolvable involution centralizer containing the chosen two-group and the
entire ambient centralizer of Q. No isolation or unique-involution
hypothesis needs to be supplied separately. -/
public theorem exists_nonsolvable_involution_centralizer_of_failed_residual_transport
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S A Q E B : Subgroup G) (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hE : 4 ≤ Nat.card E) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hno : ¬ ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ Q ∧ Q ≤ normalizer (F : Set G))
    (c : G) (hc : c ∈ centralizer (Q : Set G))
    (hfail : ¬ ElementaryCommutingConnected 2 A
      (A.map (MulAut.conj c).toMonoidHom)) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ E ∧ z ∈ Q ∧
      S ≤ centralizer ({z} : Set G) ∧
      centralizer (Q : Set G) ≤ centralizer ({z} : Set G) ∧
      centralizer ({z} : Set G) ≠ ⊤ ∧
      ¬ Group.IsSolvable (centralizer ({z} : Set G)) := by
  have hEfour := card_eq_four_of_no_normal_four Q E (hS.to_le hQS) hE hEQ hno
  have hiso := isolated_four_of_not_centralizer_transport
    S A Q E hS hA hEfour hAS hQS hEQ c hc hfail
  have hunique := unique_involution_centralizer_of_not_weak_rank_transport
    S A Q E B hS hA hE hB hAS hQS hEQ hBweak hno c hc hfail
  exact exists_nonsolvable_involution_centralizer_of_failed_isolated_transport
    S A Q B E hS hA hB hEfour hAS hQS hEQ hBweak hiso hunique c hc hfail

end Subgroup
