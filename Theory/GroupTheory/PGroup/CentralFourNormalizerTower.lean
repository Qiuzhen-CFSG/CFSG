module

public import Theory.GroupTheory.PGroup.NormalEightCentralFour
public import Theory.GroupTheory.PGroup.MaximalElementaryCentralizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PGroup.NormalizedSylowConjugation

/-!
# Central fours and the normalizer tower

A central elementary four and a distinct controlled elementary four in a finite
2-group are disjoint. Their join has order sixteen. Under an elementary order
bound of sixteen, its centralizer has that join as first omega subgroup.
The normalizer condition then supplies a conjugate four in the normalizer of
the join. Local centralizer control shows that its nonidentity elements cannot
commute with nonidentity elements of the returning four. Choosing a Sylow
subgroup of the other four's centralizer and transporting the hypotheses by
Sylow isomorphism gives the symmetric pair of auxiliary four-groups.

This is the normalizer-tower construction in Janko–Thompson, Math. Z. 113
(1970), Lemma 5.1, p.394, in
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
The rank bound and local control are explicit hypotheses, independent of any
classification or recognition theorem.
-/

open Subgroup
open scoped IsMulCommutative Pointwise
namespace Subgroup

/-- Every two-subgroup containing `B` that centralizes a nonidentity element of
`B` centralizes all of `B`. -/
@[expose] public def TwoSubgroupCentralizerControl {G : Type*} [Group G] (B : Subgroup G) : Prop :=
  ∀ w ∈ B, w ≠ 1 → ∀ Q : Subgroup G, IsPGroup 2 Q → B ≤ Q →
    Q ≤ centralizer ({w} : Set G) → Q ≤ centralizer (B : Set G)

/-- Local control separates a central four from a distinct elementary four. -/
public theorem inf_eq_bot_of_central_four_control
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (A B : Subgroup P) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : Nat.card A = 4) (hB : Nat.card B = 4) (hAc : A ≤ center P)
    (hne : B ≠ A) (hcontrol : TwoSubgroupCentralizerControl B) : A ⊓ B = ⊥ := by
  apply eq_bot_iff.mpr
  intro w hw
  by_contra hw1
  have hwne : w ≠ 1 := by simpa only [mem_bot] using hw1
  have hC : (⊤ : Subgroup P) ≤ centralizer (B : Set P) :=
    hcontrol w hw.2 hwne ⊤ (hP.to_subgroup _) le_top (by
      intro x _
      exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hAc hw.1) x))
  have hBc : B ≤ center P := by
    intro b hb
    exact mem_center_iff.mpr fun x => (hC (mem_top x) b hb).symm
  let : B.Normal := ⟨by
    intro b hb x
    simpa only [mem_center_iff.mp (hBc hb) x, mul_inv_cancel_right] using hb⟩
  have hBA := normal_elementary_le_central_four_of_no_normal_eight hno A hA hAc B
  exact hne (eq_of_le_of_card_ge hBA (by omega))

/-- A central four and a disjoint four generate a subgroup of order sixteen. -/
public theorem card_sup_eq_sixteen_of_disjoint_central_fours
    {P : Type*} [Group P] [Finite P]
    (A B : Subgroup P) (hA : Nat.card A = 4) (hB : Nat.card B = 4)
    (hAc : A ≤ center P) (hi : A ⊓ B = ⊥) : Nat.card (A ⊔ B : Subgroup P) = 16 := by
  have hnorm : B ≤ normalizer (A : Set P) := by
    intro b _
    exact centralizer_le_normalizer _ (by
      intro a ha
      exact (mem_center_iff.mp (hAc ha) b).symm)
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B hnorm
  simpa [hA, hB, hi] using h.symm

/-- One side of the central-four configuration, inside a two-group. -/
public theorem exists_four_normalizing_sup_of_central_four_control
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (A B : Subgroup P) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : Nat.card A = 4) (hB : Nat.card B = 4) (hAc : A ≤ center P)
    (hne : B ≠ A) (hcontrol : TwoSubgroupCentralizerControl B)
    (hrank : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E ≤ 16) :
    ∃ V : Subgroup P, IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧
      V ≤ normalizer ((A ⊔ B : Subgroup P) : Set P) ∧
      V ≤ centralizer (A : Set P) ∧
      ∀ v ∈ V, v ≠ 1 → ∀ b ∈ B, b ≠ 1 → ¬ Commute v b := by
  classical
  let E := A ⊔ B
  have hAB : B ≤ centralizer (A : Set P) := by
    intro b _ a ha
    exact (mem_center_iff.mp (hAc ha) b).symm
  let : A.Normal := ⟨by
    intro a ha x
    simpa only [mem_center_iff.mp (hAc ha) x, mul_inv_cancel_right] using ha⟩
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.sup_of_le_centralizer hAB
  have hi := inf_eq_bot_of_central_four_control hP hno A B hA hB hAc hne hcontrol
  have hE : Nat.card E = 16 := card_sup_eq_sixteen_of_disjoint_central_fours A B hA hB hAc hi
  have hmax : ∀ D : Subgroup P, IsElementaryAbelian 2 D → Nat.card D ≤ Nat.card E := by
    simpa only [hE] using hrank
  let Y := centralizer (E : Set P)
  let N := normalizer (Y : Set P)
  have hEY : E ≤ Y := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hNY : N = normalizer (E : Set P) := by
    apply le_antisymm
    · let : (omega₁ Y (p := 2)).Characteristic := omega₁_characteristic Y
      have h := normalizer_le_normalizer_characteristic_image Y (omega₁ Y (p := 2))
      rwa [omega_one_centralizer_map_eq_of_elementary_card_le E hmax] at h
    · exact normalizer_le_normalizer_centralizer E
  have hNproper : N < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro h
    have hnE : E.Normal := normalizer_eq_top_iff.mp (hNY.symm.trans h)
    exact hno ⟨E, hnE, inferInstance, by omega⟩
  let : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨s, hs, hsN⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent N hNproper)
  let f := (MulAut.conj s).toMonoidHom
  let V := B.map f
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map f
  have hV : Nat.card V = 4 := (card_map_of_injective (MulAut.conj s).injective).trans hB
  have hAN : A ≤ N := (le_sup_left.trans hEY).trans Y.le_normalizer
  have hBN : B ≤ N := (le_sup_right.trans hEY).trans Y.le_normalizer
  have hVN : V ≤ N := by
    rintro _ ⟨b, hb, rfl⟩
    exact (mem_normalizer_iff.mp hs b).mp (hBN hb)
  have hAf : A.map f = A := mem_normalizer_iff_map_conj_eq.mp (A.normalizer_eq_top ▸ mem_top s)
  have hVnotY : ¬ V ≤ Y := by
    intro hVY
    have hVE : V ≤ E := by
      intro v hv
      exact mem_of_pow_eq_one_of_elementary_card_le E hmax
        (elemPow_eq_one_of_isElementaryAbelian v hv) (hVY hv)
    have hEf : E.map f ≤ E := by
      dsimp [E]
      rw [map_sup, hAf]
      exact sup_le le_sup_left hVE
    have heq : E.map f = E := eq_of_le_of_card_ge hEf (by
      rw [card_map_of_injective (MulAut.conj s).injective])
    exact hsN (hNY ▸ mem_normalizer_iff_map_conj_eq.mpr heq)
  have hVA : V ⊓ A = ⊥ := by
    have h := congrArg (fun D : Subgroup P => D.map f) hi
    rw [map_inf _ _ _ (MulAut.conj s).injective, hAf, map_bot] at h
    simpa only [inf_comm] using h
  have hCY : centralizer (B : Set P) ≤ Y := by
    intro x hx
    have hEC : E ≤ centralizer ({x} : Set P) := by
      apply sup_le
      · intro a ha
        exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hAc ha) x).symm
      · intro b hb
        exact mem_centralizer_singleton_iff.mpr (hx b hb)
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hEC hy)
  have hVY : V ⊓ Y = ⊥ := by
    apply eq_bot_iff.mpr
    intro v hv
    by_contra hv1
    have hvne : v ≠ 1 := by simpa only [mem_bot] using hv1
    have hvE : v ∈ E := mem_of_pow_eq_one_of_elementary_card_le E hmax
      (elemPow_eq_one_of_isElementaryAbelian v hv.1) hv.2
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_left.mp hvE
    have hbne : b ≠ 1 := by
      intro hb1
      have hva : v ∈ A := by
        have hav : a = v := by simpa [hb1] using hab
        exact hav ▸ ha
      have : v ∈ V ⊓ A := ⟨hv.1, hva⟩
      rw [hVA] at this
      exact hvne this
    have hVCb : V ≤ centralizer ({b} : Set P) := by
      intro x hx
      apply mem_centralizer_singleton_iff.mpr
      have hxv : x * v = v * x := congrArg Subtype.val
        (mul_comm (⟨x, hx⟩ : V) ⟨v, hv.1⟩)
      have hxa := mem_center_iff.mp (hAc ha) x
      apply mul_left_cancel (a := a)
      calc
        a * (x * b) = x * (a * b) := by rw [← mul_assoc, ← hxa, mul_assoc]
        _ = a * b * x := by rw [hab, hxv]
        _ = a * (b * x) := mul_assoc _ _ _
    have hBCb : B ≤ centralizer ({b} : Set P) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (mul_comm (⟨x, hx⟩ : B) ⟨b, hb⟩))
    have hVCB : V ≤ centralizer (B : Set P) := le_sup_right.trans
      (hcontrol b hb hbne (B ⊔ V) (hP.to_subgroup _) le_sup_left (sup_le hBCb hVCb))
    exact hVnotY (hVCB.trans hCY)
  refine ⟨V, inferInstance, hV, hNY ▸ hVN, ?_, ?_⟩
  · intro v _ a ha
    exact (mem_center_iff.mp (hAc ha) v).symm
  · intro v hv hvne b hb hbne hcomm
    have hBCb : B ≤ centralizer ({b} : Set P) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (mul_comm (⟨x, hx⟩ : B) ⟨b, hb⟩))
    have hzCb : zpowers v ≤ centralizer ({b} : Set P) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hcomm.eq)
    have hvCB := hcontrol b hb hbne (B ⊔ zpowers v) (hP.to_subgroup _)
      le_sup_left (sup_le hBCb hzCb) ((le_sup_right : zpowers v ≤ B ⊔ zpowers v) (mem_zpowers v))
    have hvY : v ∈ Y := hCY hvCB
    have : v ∈ V ⊓ Y := ⟨hv, hvY⟩
    rw [hVY] at this
    exact hvne this
end Subgroup

namespace Subgroup

/-- Centralizer control restricts to an overgroup of the controlled subgroup. -/
public theorem TwoSubgroupCentralizerControl.subgroupOf
    {G : Type*} [Group G] {B S : Subgroup G}
    (hcontrol : TwoSubgroupCentralizerControl B) (hBS : B ≤ S) :
    TwoSubgroupCentralizerControl (B.subgroupOf S) := by
  intro w hw hwne Q hQ hBQ hQw
  have hBmap : B ≤ Q.map S.subtype := by
    rw [← map_subgroupOf_eq_of_le hBS]
    exact map_mono hBQ
  have hmapC : Q.map S.subtype ≤ centralizer ({(w : G)} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hQw hq)))
  have h := hcontrol (w : G) hw (fun he => hwne (Subtype.ext he))
    (Q.map S.subtype) (hQ.map _) hBmap hmapC
  intro q hq b hb
  apply Subtype.ext
  exact h (mem_map_of_mem _ hq) b hb

/-- Map the one-sided tower configuration from a two-subgroup to its ambient group. -/
public theorem exists_ambient_four_normalizing_sup_of_central_four_control
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) (hS : IsPGroup 2 S)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : Nat.card A = 4) (hB : Nat.card B = 4) (hAS : A ≤ S) (hBS : B ≤ S)
    (hSC : S ≤ centralizer (A : Set G)) (hne : B ≠ A)
    (hcontrol : TwoSubgroupCentralizerControl B)
    (hrank : ∀ E : Subgroup S, IsElementaryAbelian 2 E → Nat.card E ≤ 16) :
    A ⊓ B = ⊥ ∧ ∃ V : Subgroup G, IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧
      V ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) ∧
      V ≤ centralizer (A : Set G) ∧
      ∀ v ∈ V, v ≠ 1 → ∀ b ∈ B, b ≠ 1 → ¬ Commute v b := by
  let A' := A.subgroupOf S
  let B' := B.subgroupOf S
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.subgroupOf hAS
  let : IsElementaryAbelian 2 B' := IsElementaryAbelian.subgroupOf hBS
  have hA' : Nat.card A' = 4 := (Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv).trans hA
  have hB' : Nat.card B' = 4 := (Nat.card_congr (subgroupOfEquivOfLe hBS).toEquiv).trans hB
  have hAc : A' ≤ center S := by
    intro a ha
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    exact (hSC s.property a ha).symm
  have hne' : B' ≠ A' := by
    intro he
    apply hne
    have hm := congrArg (fun D : Subgroup S => D.map S.subtype) he
    simpa only [A', B', map_subgroupOf_eq_of_le hBS, map_subgroupOf_eq_of_le hAS] using hm
  have hc := hcontrol.subgroupOf hBS
  have hi := inf_eq_bot_of_central_four_control hS hno A' B' hA' hB' hAc hne' hc
  have hiG := congrArg (fun D : Subgroup S => D.map S.subtype) hi
  rw [map_inf _ _ _ S.subtype_injective, map_subgroupOf_eq_of_le hAS,
    map_subgroupOf_eq_of_le hBS, map_bot] at hiG
  refine ⟨hiG, ?_⟩
  obtain ⟨V, hVe, hV4, hVN, hVC, hVfree⟩ :=
    exists_four_normalizing_sup_of_central_four_control hS hno A' B' hA' hB' hAc hne' hc hrank
  let := hVe
  refine ⟨V.map S.subtype, IsElementaryAbelian.map _,
    (card_map_of_injective S.subtype_injective).trans hV4, ?_, ?_, ?_⟩
  · have h := (map_mono hVN).trans (le_normalizer_map S.subtype)
    rw [map_sup, map_subgroupOf_eq_of_le hAS, map_subgroupOf_eq_of_le hBS] at h
    exact h
  · rintro _ ⟨v, hv, rfl⟩ a ha
    exact congrArg Subtype.val (hVC hv (⟨a, hAS ha⟩ : S) ha)
  · rintro _ ⟨v, hv, rfl⟩ hvne b hb hbne hcomm
    apply hVfree v hv (fun he => hvne (congrArg Subtype.val he)) ⟨b, hBS hb⟩ hb
      (fun he => hbne (congrArg Subtype.val he))
    exact Subtype.ext hcomm.eq

/-- Centralizer control and a central Sylow conjugate let us choose a Sylow
containing a prescribed two-subgroup of the centralizer. -/
private theorem exists_sylow_le_centralizer_containing
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (R : Sylow p G) (C E : Subgroup G) (hRC : (R : Subgroup G) ≤ C)
    (hE : IsPGroup p E) (hEC : E ≤ C) :
    ∃ T : Sylow p G, E ≤ (T : Subgroup G) ∧ (T : Subgroup G) ≤ C := by
  obtain ⟨c, hc, hER⟩ := IsPGroup.exists_conj_le_sylow_of_normalized R C E
    (hRC.trans C.le_normalizer) hE hEC
  refine ⟨c⁻¹ • R, ?_, ?_⟩
  · intro e he
    change e ∈ (R : Subgroup G).map (MulAut.conj c⁻¹).toMonoidHom
    refine ⟨MulAut.conj c e, hER (mem_map_of_mem _ he), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · exact Sylow.smul_le hRC (⟨c⁻¹, C.inv_mem hc⟩ : C)

end Subgroup

namespace Sylow

/-- A distinct returning conjugate of a central four gives the symmetric pair
of auxiliary fours in the normalizer of their elementary sixteen. The local
control and elementary order bound are supplied explicitly. -/
public theorem exists_central_four_normalizer_configuration
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hWc : W ≤ center S)
    (hrank : ∀ E : Subgroup S, IsElementaryAbelian 2 E → Nat.card E ≤ 16)
    (hcontrol : ∀ k : G, TwoSubgroupCentralizerControl
      ((W.map (S : Subgroup G).subtype).map (MulAut.conj k).toMonoidHom))
    (g : G)
    (hBS : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G))
    (hne : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≠
      W.map (S : Subgroup G).subtype) :
    let A := W.map (S : Subgroup G).subtype
    let B := A.map (MulAut.conj g).toMonoidHom
    A ⊓ B = ⊥ ∧ ∃ V V₁ : Subgroup G,
      IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧
      IsElementaryAbelian 2 V₁ ∧ Nat.card V₁ = 4 ∧
      V ⊔ V₁ ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) ∧
      V ≤ centralizer (A : Set G) ∧ V₁ ≤ centralizer (B : Set G) ∧
      (∀ v ∈ V, v ≠ 1 → ∀ b ∈ B, b ≠ 1 → ¬ Commute v b) ∧
      (∀ v ∈ V₁, v ≠ 1 → ∀ a ∈ A, a ≠ 1 → ¬ Commute v a) := by
  classical
  let A := W.map (S : Subgroup G).subtype
  let B := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hA : Nat.card A = 4 := (card_map_of_injective (S : Subgroup G).subtype_injective).trans hW
  have hB : Nat.card B = 4 := (card_map_of_injective (MulAut.conj g).injective).trans hA
  have hAS : A ≤ (S : Subgroup G) := map_subtype_le W
  have hSA : (S : Subgroup G) ≤ centralizer (A : Set G) := by
    intro s hs a ha
    obtain ⟨a, ha, rfl⟩ := ha
    exact (congrArg Subtype.val (mem_center_iff.mp (hWc ha) (⟨s, hs⟩ : S))).symm
  have hBc : TwoSubgroupCentralizerControl B := hcontrol g
  have hAc : TwoSubgroupCentralizerControl A := by
    have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    simpa only [h1, map_id] using hcontrol 1
  obtain ⟨hi, V, hVe, hV4, hVN, hVC, hVfree⟩ :=
    exists_ambient_four_normalizing_sup_of_central_four_control (S : Subgroup G) S.isPGroup'
      hno A B hA hB hAS hBS hSA hne hBc hrank
  let E := A ⊔ B
  have hBA : B ≤ centralizer (A : Set G) := hBS.trans hSA
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.sup_of_le_centralizer hBA
  have hEC : E ≤ centralizer (B : Set G) := sup_le (le_centralizer_iff.mp hBA)
    (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  let R : Sylow 2 G := S.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hRC : (R : Subgroup G) ≤ centralizer (B : Set G) := by
    rintro _ ⟨s, hs, rfl⟩ b hb
    obtain ⟨a, ha, rfl⟩ := hb
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj g) (hSA hs a ha)
  obtain ⟨T, hET, hTC⟩ := exists_sylow_le_centralizer_containing R
    (centralizer (B : Set G)) E hRC (IsElementaryAbelian.isPGroup 2 E) hEC
  let e : T ≃* S := T.equiv S
  have hnoT : ¬ ∃ D : Subgroup T, D.Normal ∧ IsElementaryAbelian 2 D ∧ 8 ≤ Nat.card D := by
    rintro ⟨D, hDn, hDe, hD8⟩
    let := hDe
    apply hno
    refine ⟨D.map e.toMonoidHom, hDn.map _ e.surjective, IsElementaryAbelian.map _, ?_⟩
    rwa [card_map_of_injective e.injective]
  have hrankT : ∀ D : Subgroup T, IsElementaryAbelian 2 D → Nat.card D ≤ 16 := by
    intro D hD
    let := hD
    have h := hrank (D.map e.toMonoidHom) (IsElementaryAbelian.map _)
    rwa [card_map_of_injective e.injective] at h
  obtain ⟨_, V₁, hV₁e, hV₁4, hV₁N, hV₁C, hV₁free⟩ :=
    exists_ambient_four_normalizing_sup_of_central_four_control (T : Subgroup G) T.isPGroup'
      hnoT B A hB hA (le_sup_right.trans hET) (le_sup_left.trans hET) hTC
      (Ne.symm hne) hAc hrankT
  refine ⟨hi, V, V₁, hVe, hV4, hV₁e, hV₁4, sup_le hVN ?_, hVC, hV₁C, hVfree, hV₁free⟩
  simpa only [sup_comm] using hV₁N

end Sylow
