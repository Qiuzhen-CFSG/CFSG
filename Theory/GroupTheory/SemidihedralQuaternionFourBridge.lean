module
public import Theory.GroupTheory.SemidihedralFourCentralizer
public import Theory.GroupTheory.ElementaryCommutingConnectivity
public import Theory.GroupTheory.ElementaryFourExtension
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The centralizer-envelope obstruction to a semidihedral four-group bridge

Let `Q` have an explicit semidihedral presentation, and suppose that `C_G(Q)`
has a unique involution. The canonical four-group `E` of `Q` is an isolated
vertex in the elementary commuting graph of `H = Q C_G(Q)`. Hence an
elementary subgroup `B` of order at least eight in `H` cannot be connected
to `E` by a path contained in `H`.

For the proof, the presentation gives `C_Q(E) = E` and a central involution
`z` in `E`. If an involution `x = q c` in `H` centralizes `E`, then `q`
centralizes `E`, so `q` lies in `E`. Since `q` and `c` commute, `c` also has
exponent two. Uniqueness of the involution of `C_G(Q)` puts `c` in `{1,z}`.
Thus `x` lies in `E`. Apply this pointwise to elementary neighbors, and then
induct on a commuting path inside `H`.

In a finite simple group containing `B`, the ambient four-group extension
theorem nevertheless supplies an elementary extension of `E` of order at
least eight. Every such extension leaves `H`. Thus these results are
compatible with ambient connectivity, and identify the need for fusion
outside the entire envelope in an ambient bridge proof. The local
quaternion and nonsolvability hypotheses are unnecessary for this obstruction.

Context: the proposed semidihedral-quaternion route to the binary fusion
remark following GLS2, Proposition 22.4 (`refs/KGroup/GLS2/ChapterF.tex`).
The ambient extension comes from the general argument of GLS4, Lemma 18.1
(`refs/KGroup/GLS4/Chapter2.tex`); later results there assume K-properness.
The envelope obstruction is an independent elementary calculation, rather
than an assertion of either source's ambient connectivity conclusion.
-/

open scoped Pointwise

namespace Subgroup

/-- An element of exponent two in the centralizer envelope centralizing a
self-centralizing elementary subgroup belongs to that subgroup, when the
unique centralizer involution also belongs to it. -/
public theorem pow_two_mem_of_mem_centralizer_envelope
    {G : Type*} [Group G] (Q E : Subgroup G)
    [IsElementaryAbelian 2 E] (hEQ : E ≤ Q)
    (hself : Q ⊓ centralizer (E : Set G) ≤ E)
    (z : G) (hzE : z ∈ E) (hzC : z ∈ centralizer (Q : Set G))
    (hz : orderOf z = 2)
    (hunique : ∃! t : centralizer (Q : Set G), orderOf t = 2)
    (x : G) (hx : x ∈ Q ⊔ centralizer (Q : Set G))
    (hxC : x ∈ centralizer (E : Set G)) (hx2 : x ^ 2 = 1) : x ∈ E := by
  have hprod : x ∈ (Q : Set G) * (centralizer (Q : Set G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left Q _ (centralizer_le_normalizer _)]
    exact hx
  obtain ⟨q, hq, c, hc, rfl⟩ := hprod
  have hqC : q ∈ centralizer (E : Set G) := by
    have h := (centralizer (E : Set G)).mul_mem hxC
      ((centralizer (E : Set G)).inv_mem (centralizer_le hEQ hc))
    simpa only [mul_inv_cancel_right] using h
  have hqE : q ∈ E := hself ⟨hq, hqC⟩
  have hq2 : q ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) q hqE
  have hc2 : c ^ 2 = 1 := by
    have hqc : Commute q c := hc q hq
    simpa only [hqc.mul_pow, hq2, one_mul] using hx2
  have hcE : c ∈ E := by
    by_cases hc1 : c = 1
    · exact hc1 ▸ E.one_mem
    have hcorder : orderOf (⟨c, hc⟩ : centralizer (Q : Set G)) = 2 := by
      rw [← orderOf_coe]
      exact orderOf_eq_prime hc2 hc1
    have hzorder : orderOf (⟨z, hzC⟩ : centralizer (Q : Set G)) = 2 := by
      rwa [← orderOf_coe]
    have hcz : c = z := congrArg Subtype.val (hunique.unique hcorder hzorder)
    exact hcz ▸ hzE
  exact E.mul_mem hqE hcE

/-- Every elementary neighbor inside the centralizer envelope lies in the
self-centralizing elementary subgroup containing the unique involution. -/
public theorem elementary_le_of_le_centralizer_envelope
    {G : Type*} [Group G] (Q E : Subgroup G)
    [IsElementaryAbelian 2 E] (hEQ : E ≤ Q)
    (hself : Q ⊓ centralizer (E : Set G) ≤ E)
    (z : G) (hzE : z ∈ E) (hzC : z ∈ centralizer (Q : Set G))
    (hz : orderOf z = 2)
    (hunique : ∃! t : centralizer (Q : Set G), orderOf t = 2)
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hWH : W ≤ Q ⊔ centralizer (Q : Set G))
    (hWC : W ≤ centralizer (E : Set G)) : W ≤ E := by
  intro w hw
  exact pow_two_mem_of_mem_centralizer_envelope Q E hEQ hself
    z hzE hzC hz hunique w (hWH hw) (hWC hw)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw)

/-- If all elementary subgroups centralizing a four-group are contained in it,
its elementary commuting component is a singleton. -/
public theorem eq_of_elementaryCommutingConnected_of_elementary_centralizer_bound
    {G : Type*} [Group G] [Finite G] (E W : Subgroup G)
    (hE : Nat.card E = 4)
    (hbound : ∀ V : Subgroup G, IsElementaryAbelian 2 V →
      V ≤ centralizer (E : Set G) → V ≤ E)
    (hpath : ElementaryCommutingConnected 2 E W) : W = E := by
  have h := hpath.2.2
  clear hpath
  induction h with
  | refl => rfl
  | @tail V W hpath hstep ih =>
    have hWE : W ≤ E := hbound W hstep.2.2.1 (by
      rw [← ih]
      exact le_centralizer_iff.mp hstep.2.2.2.2)
    exact eq_of_le_of_card_ge hWE (by have := hstep.2.2.2.1; norm_num at this; omega)

/-- An isolated four-group inside an envelope is disconnected there from a
subgroup of order at least eight. Both endpoints and the path are intrinsic
to the envelope; this makes no assertion about ambient connectivity. -/
public theorem not_connected_subgroupOf_of_elementary_centralizer_bound
    {G : Type*} [Group G] [Finite G] (H B E : Subgroup G)
    (hBH : B ≤ H) (hEH : E ≤ H) (hB : 8 ≤ Nat.card B) (hE : Nat.card E = 4)
    (hbound : ∀ W : Subgroup G, IsElementaryAbelian 2 W →
      W ≤ H → W ≤ centralizer (E : Set G) → W ≤ E) :
    ¬ ElementaryCommutingConnected 2 (B.subgroupOf H) (E.subgroupOf H) := by
  intro hpath
  have heq := eq_of_elementaryCommutingConnected_of_elementary_centralizer_bound
    (E.subgroupOf H) (B.subgroupOf H)
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv])
    (fun W hWe hWC => ?_) hpath.symm
  · have hcard := congrArg (fun K : Subgroup H => Nat.card K) heq
    rw [Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv] at hcard
    omega
  · let : IsElementaryAbelian 2 W := hWe
    have hm : W.map H.subtype ≤ E := hbound _ (IsElementaryAbelian.map H.subtype)
      (map_subtype_le _) (by
        rintro w ⟨x, hx, rfl⟩ e he
        exact congrArg Subtype.val (hWC hx ⟨e, hEH he⟩ he))
    intro w hw
    exact hm (mem_map.mpr ⟨w, hw, rfl⟩)

end Subgroup

namespace Semidihedral

/-- The canonical semidihedral four-group has no distinct elementary commuting
neighbor inside `Q C_G(Q)` when the latter centralizer has a unique involution. -/
public theorem exists_four_with_envelope_bound
    {G : Type*} [Group G] (Q : Subgroup G)
    {n : ℕ} (hn : 4 ≤ n) (a b : Q)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set Q) = ⊤)
    (hunique : ∃! t : Subgroup.centralizer (Q : Set G), orderOf t = 2) :
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧ E ≤ Q ∧
      ∀ W : Subgroup G, IsElementaryAbelian 2 W →
        W ≤ Q ⊔ Subgroup.centralizer (Q : Set G) →
        W ≤ Subgroup.centralizer (E : Set G) → W ≤ E := by
  let F := Subgroup.closure ({a ^ (2 ^ (n - 2)), b} : Set Q)
  obtain ⟨hFe, hF⟩ := canonical_four hn a b ha hb hconj hgen
  let : IsElementaryAbelian 2 F := hFe
  let E := F.map Q.subtype
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map Q.subtype
  have hEQ : E ≤ Q := Subgroup.map_subtype_le _
  have hself : Q ⊓ Subgroup.centralizer (E : Set G) ≤ E := by
    intro q hq
    have hqF : (⟨q, hq.1⟩ : Q) ∈ Subgroup.centralizer (F : Set Q) := by
      intro f hf
      apply Subtype.ext
      exact hq.2 f (Subgroup.mem_map.mpr ⟨f, hf, rfl⟩)
    rw [centralizer_canonical_four hn a b ha hb hconj hgen] at hqF
    exact Subgroup.mem_map.mpr ⟨⟨q, hq.1⟩, hqF, rfl⟩
  let z := a ^ (2 ^ (n - 2))
  have hz : orderOf z = 2 := by
    dsimp [z]
    rw [orderOf_pow_of_dvd (by positivity)
      (by rw [ha]; exact pow_dvd_pow 2 (by omega)), ha]
    rw [show n - 1 = n - 2 + 1 by omega, pow_succ,
      Nat.mul_div_right _ (by positivity)]
  have hzF : z ∈ F := Subgroup.subset_closure (by simp [z])
  have hzZ : z ∈ Subgroup.center Q := by
    rw [center_eq hn a b ha hb hconj hgen]
    exact Subgroup.mem_zpowers z
  have hzC : (z : G) ∈ Subgroup.centralizer (Q : Set G) := by
    intro q hq
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨q, hq⟩)
  refine ⟨E, inferInstance, ?_, hEQ, ?_⟩
  · rwa [Subgroup.card_map_of_injective Q.subtype_injective]
  · intro W hWe hWH hWC
    let : IsElementaryAbelian 2 W := hWe
    exact Subgroup.elementary_le_of_le_centralizer_envelope Q E hEQ hself
      z (Subgroup.mem_map.mpr ⟨z, hzF, rfl⟩) hzC
      (by simpa only [Subgroup.orderOf_coe] using hz) hunique W hWH hWC

/-- The canonical four-group is disconnected from `B` inside `Q C_G(Q)`,
even though simplicity supplies an ambient elementary extension of order
at least eight. That extension necessarily leaves the entire envelope. -/
public theorem exists_four_with_envelope_obstruction_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (Q B : Subgroup G) [IsElementaryAbelian 2 B] (hB : 8 ≤ Nat.card B)
    (hBH : B ≤ Q ⊔ Subgroup.centralizer (Q : Set G))
    (hsd : ∃ n : ℕ, 4 ≤ n ∧ Nat.card Q = 2 ^ n ∧
      ∃ a b : Q, orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
        b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧
        Subgroup.closure ({a, b} : Set Q) = ⊤)
    (hunique : ∃! t : Subgroup.centralizer (Q : Set G), orderOf t = 2) :
    let H := Q ⊔ Subgroup.centralizer (Q : Set G)
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧ E ≤ Q ∧
      (∀ W : Subgroup G, IsElementaryAbelian 2 W → W ≤ H →
        W ≤ Subgroup.centralizer (E : Set G) → W ≤ E) ∧
      ¬ Subgroup.ElementaryCommutingConnected 2 (B.subgroupOf H) (E.subgroupOf H) ∧
      ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A ∧ E ≤ A ∧ ¬ A ≤ H := by
  obtain ⟨n, hn, -, a, b, ha, hb, hconj, hgen⟩ := hsd
  obtain ⟨E, hEe, hE, hEQ, hbound⟩ :=
    exists_four_with_envelope_bound Q hn a b ha hb hconj hgen hunique
  let : IsElementaryAbelian 2 E := hEe
  refine ⟨E, hEe, hE, hEQ, hbound,
    Subgroup.not_connected_subgroupOf_of_elementary_centralizer_bound _ B E
      hBH (hEQ.trans le_sup_left) hB hE hbound, ?_⟩
  obtain ⟨A, hAe, hA, hEA⟩ :=
    Subgroup.exists_elementary_eight_above_four_of_simple B E hB hE
  let : IsElementaryAbelian 2 A := hAe
  refine ⟨A, hAe, hA, hEA, ?_⟩
  intro hAH
  have hAC : A ≤ Subgroup.centralizer (E : Set G) :=
    A.le_centralizer.trans (Subgroup.centralizer_le hEA)
  have hcard := Subgroup.card_le_of_le (hbound A hAe hAH hAC)
  omega

end Semidihedral
