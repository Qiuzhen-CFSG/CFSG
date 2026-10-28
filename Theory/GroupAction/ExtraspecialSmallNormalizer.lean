module
public import Theory.GroupTheory.CentralQuotientMovedNormalizer
public import Theory.GroupTheory.PGroup.IndexTwoFixedAutomorphism
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Fully moved sections with a small normalizer in an extraspecial core

Let Q be a normal self-centralizing extraspecial two-group. A perfect
subgroup B with normalizer index at most two in Q is normalized by Q.
The commutator [Q,B] lies in O₂(B). Rigidity of the original elementary
section E therefore makes Q intersect its centralizer in index at most two.
Every involution in E then acts trivially on Q/Z(Q): an involutive
automorphism fixing an index-two subgroup and all squares has central
displacement. Since Z(Q) has order two, B fixes it. The three-subgroup
lemma and E=[E,B] give [E,Q]=1. Consequently E lies in Z(Q) and has
order at most two.

The overgroup version retains an ambient Sylow and both literal
normalizers; no containment of Q in that Sylow is assumed.
Source application: Aschbacher--Smith, proof of 12.6.12, pp.825--826,
for the first native J₄ involution centralizer.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Rigidity and an index-at-most-two simultaneous normalizer put the whole moved section in the core center. -/
theorem small_core_normalizer_bound (Q B E : Subgroup G)
    [Q.Normal] [IsExtraspecial 2 Q] [Group.IsPerfect B]
    (hQ : IsPGroup 2 Q) (hC : centralizer (Q : Set G) ≤ Q)
    (hE : IsElementaryAbelian 2 E) (hmove : ⁅E,B⁆ = E)
    (hfix : ∀ r ∈ normalizer (B : Set G) ⊓ normalizer (E : Set G),
      (∀ b ∈ B, ⁅r,b⁆ ∈ B.pCoreIn 2) → r ∈ centralizer (E : Set G))
    (hi : (normalizer (B : Set G) ⊓ normalizer (E : Set G)).relIndex Q ≤ 2) :
    Nat.card E ≤ 2 := by
  let Z := (center Q).map Q.subtype
  have hZcard : Nat.card Z = 2 := by
    rw [card_map_of_injective Q.subtype_injective, IsExtraspecial.center_order_p 2 Q]
  have hGZ : (⊤ : Subgroup G) ≤ centralizer (Z : Set G) :=
    (le_normalizer_of_normal.trans (normalizer_le_normalizer_characteristic_image Q (center Q))).trans
      (normalizer_le_centralizer_of_card_two Z hZcard)
  have hZB : Z ≤ centralizer (B : Set G) :=
    le_centralizer_iff.mp (le_top.trans hGZ)
  have hBQ : B ≤ normalizer (Q : Set G) := le_normalizer_of_normal
  let : Group.IsNilpotent Q := hQ.isNilpotent
  have hn := normal_in_sup_of_perfect_of_solvable_of_small_normalizer B Q hBQ
    (((relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite).trans hi).trans (by decide : 2 ≤ 4))
  have hQB : Q ≤ normalizer (B : Set G) := le_sup_right.trans
    ((normal_subgroupOf_iff_le_normalizer (show B ≤ B ⊔ Q from le_sup_left)).mp hn)
  have hcomm : ⁅Q,B⁆ ≤ B.pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      (hQ.to_le (le_normalizer_iff_commutator_le_left.mp hBQ))
      (le_normalizer_iff_commutator_le_right.mp hQB)
      (normalizer_commutator_ge_right Q B)
  have hR : Q ⊓ normalizer (E : Set G) ≤ centralizer (E : Set G) := by
    rintro r ⟨hr,hrE⟩
    exact hfix r ⟨hQB hr,hrE⟩ (fun b hb => hcomm (commutator_mem_commutator hr hb))
  have hCQ : (centralizer (E : Set G)).relIndex Q ≤ 2 := by
    have hn : Q ⊓ (normalizer (B : Set G) ⊓ normalizer (E : Set G)) ≤
        centralizer (E : Set G) := by
      rintro r ⟨hr,_,hrE⟩
      exact hR ⟨hr,hrE⟩
    have hb := (relIndex_le_of_le_left hn
      (index_ne_zero_of_finite : (Q ⊓ (normalizer (B : Set G) ⊓ normalizer (E : Set G))).relIndex Q ≠ 0))
    simpa only [inf_relIndex_left] using hb.trans (by simpa only [inf_relIndex_left] using hi)
  have hcore : B.pCoreIn 2 ≤ centralizer (E : Set G) := by
    intro r hr
    have hrB := pCoreIn_le 2 B hr
    have hBE : B ≤ normalizer (E : Set G) :=
      le_normalizer_iff_commutator_le_left.mpr hmove.le
    exact hfix r ⟨B.le_normalizer hrB,hBE hrB⟩ (fun b hb =>
      le_normalizer_iff_commutator_le_left.mp
        (B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
        (commutator_mem_commutator hr hb))
  have hEQ : ⁅E,Q⁆ ≤ Z := by
    apply commutator_le.mpr
    intro e he q hq
    let a := MulAut.conjNormal (H := Q) e
    let D := (centralizer (E : Set G)).subgroupOf Q
    have hD : D.index ≤ 2 := hCQ
    have ha2 : a ^ 2 = 1 := by
      rw [←map_pow]
      have he2 : e^2=1 := elemPow_eq_one_of_isElementaryAbelian _ he
      rw [he2,map_one]
    have hfixD (d : Q) (hd : d ∈ D) : a d = d := by
      apply Subtype.ext
      change e * (d : G) * e⁻¹ = d
      have hc : e * (d : G) = (d : G) * e := mem_centralizer_iff.mp hd e he
      rw [hc,mul_inv_cancel_right]
    have hsquare (q : Q) : a (q^2) = q^2 := by
      apply Subtype.ext
      change e * ((q : G)^2) * e⁻¹ = (q : G)^2
      have hc := hGZ (mem_top e) _ (mem_map_of_mem Q.subtype (IsExtraspecial.square_mem_center q))
      change (q : G)^2 * e = e * (q : G)^2 at hc
      rw [←hc,mul_inv_cancel_right]
    have haquot : quotientAut (center Q) a = 1 := by
      by_cases h1 : D.index = 1
      · have ht := index_eq_one.mp h1
        have haone : a = 1 := MulEquiv.ext (fun d => hfixD d (ht ▸ mem_top d))
        rw [haone,map_one]
      · have hpos : D.index ≠ 0 := index_ne_zero_of_finite
        exact quotientAut_eq_one_of_involutive_fixed_index_two D (by omega) a ha2 hfixD hsquare
    have hh := DFunLike.congr_fun haquot (QuotientGroup.mk' (center Q) ⟨q,hq⟩)
    rw [quotientAut_apply_mk, MulAut.one_apply] at hh
    have hz := QuotientGroup.eq_iff_div_mem.mp hh
    exact ⟨a ⟨q,hq⟩ / (⟨q,hq⟩ : Q),hz,by change (e*q*e⁻¹)/q = ⁅e,q⁆; rw [div_eq_mul_inv,commutatorElement_def]⟩
  have hzero : ⁅⁅E,B⁆,Q⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate
    (commutator_eq_bot_iff_le_centralizer.mpr (by rw [commutator_comm B Q]; exact hcomm.trans hcore))
    (commutator_eq_bot_iff_le_centralizer.mpr (by rw [commutator_comm Q E]; exact hEQ.trans hZB))
  rw [hmove] at hzero
  have hEC := commutator_eq_bot_iff_le_centralizer.mp hzero
  have hEZ : E ≤ Z := by
    intro e he
    refine ⟨⟨e,hC (hEC he)⟩,mem_center_iff.mpr (fun q => Subtype.ext (hEC he q q.property)),rfl⟩
  exact (card_le_of_le hEZ).trans_eq hZcard
end Subgroup

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Apply the bound in a literal overgroup, retaining the original ambient Sylow intersection. -/
theorem moved_card_le_two_in_extraspecial_overgroup
    (P : Sylow 2 G) (B E K : Subgroup G) [Group.IsPerfect B]
    (hE : IsElementaryAbelian 2 E) (hm : ⁅E,B⁆ = E)
    (hBK : B ≤ K) (hEK : E ≤ K)
    (hQ : IsExtraspecial 2 (pCore 2 K))
    (hC : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hfix : ∀ r ∈ normalizer (B : Set G) ⊓ normalizer (E : Set G),
      (∀ b ∈ B, ⁅r,b⁆ ∈ B.pCoreIn 2) → r ∈ centralizer (E : Set G))
    (hi : (normalizer (B : Set G) ⊓ normalizer (E : Set G) ⊓ K).relIndex
      (P : Subgroup G) ≤ 2) : Nat.card E ≤ 2 := by
  let Q := (pCore 2 K).map K.subtype
  let N := normalizer (B : Set G) ⊓ normalizer (E : Set G) ⊓ K
  have hKQ : K ≤ normalizer (Q : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hiQ := (relIndex_pGroup_le_sylow_of_normalizes P N Q
    (pCore_isPGroup.map K.subtype) (inf_le_right.trans hKQ)).trans hi
  have hn : N.subgroupOf K =
      normalizer (B.subgroupOf K : Set K) ⊓ normalizer (E.subgroupOf K : Set K) := by
    rw [←subgroupOf_normalizer_eq hBK,←subgroupOf_normalizer_eq hEK]
    ext x
    change ((x : G) ∈ normalizer (B : Set G) ∧ (x : G) ∈ normalizer (E : Set G)) ∧
      (x : G) ∈ K ↔ (x : G) ∈ normalizer (B : Set G) ∧ (x : G) ∈ normalizer (E : Set G)
    exact ⟨fun hx => hx.1,fun hx => ⟨hx,x.property⟩⟩
  have hi' : (normalizer (B.subgroupOf K : Set K) ⊓
      normalizer (E.subgroupOf K : Set K)).relIndex (pCore 2 K) ≤ 2 := by
    rw [←hn]
    change (N.comap K.subtype).relIndex (pCore 2 K) ≤ 2
    rw [relIndex_comap]
    exact hiQ
  let : Group.IsPerfect (B.subgroupOf K) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBK).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBK).symm.surjective
  have hm' : ⁅E.subgroupOf K,B.subgroupOf K⁆ = E.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hBK,map_subgroupOf_eq_of_le hEK,hm]
  have hh := small_core_normalizer_bound (pCore 2 K) (B.subgroupOf K) (E.subgroupOf K)
    pCore_isPGroup hC (IsElementaryAbelian.subgroupOf hEK) hm'
    (core_rigidity_subgroupOf K B E hBK hEK hfix) hi'
  rwa [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv] at hh
end Subgroup
