module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalCubic
public import Theory.SpecificGroups.Alternating.FourThirdCentralizer
public import Theory.GroupTheory.ClassTwoCommutator
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PGroup.SmallClassInvolutions
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalAlternatingCore

/-!
# The alternating-four residual yields the symmetric-four factor

The conjugation action on the actual A4 residual has two-group kernel and
is onto S4. Goldschmidt's characteristic small-class involution span gives
an involution outside O2(G). The third lower-central term is killed by the
characteristic obstruction, so the involution centralizes the complementary
core factor. Adjoining it to the residual gives a subgroup of order 24,
faithfully acting as S4; multiplication supplies the actual direct product.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), proof of
(2.14), printed p.385. The core decomposition and conjugation marking are
reused from `LocalAlternatingCore`.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] [Finite G]

theorem local_sylow_class_two_of_alternating
    (P : Sylow 2 G)
    (hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup G).subtype).Normal)
    (eR : pResidual 2 G ≃* alternatingGroup (Fin 4)) :
    _root_.commutator P ≤ center P := by
  let K := (⊤ : Subgroup P).lowerCentralSeries 2
  let M := K.map (P : Subgroup G).subtype
  have hc : M ≤ centralizer ((pResidual 2 G : Subgroup G) : Set G) :=
    alternatingGroup.FourThirdCentralizer.third_centralizes
      (P : Subgroup G) (pResidual 2 G) P.isPGroup'
      (by rw [normalizer_eq_top]; exact le_top) eR
  have hPM : (P : Subgroup G) ≤ normalizer (M : Set G) := by
    have hh := K.le_normalizer_map (P : Subgroup G).subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hRM : pResidual 2 G ≤ normalizer (M : Set G) :=
    (le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)
  have hM : M.Normal := normalizer_eq_top_iff.mp
    (top_unique ((pResidual_sup_sylow_eq_top P).symm.le.trans (sup_le hRM hPM)))
  have hk : K = ⊥ := by
    by_contra hn
    exact hP K inferInstance hn hM
  exact commutator_top_right_eq_bot_iff_le_center.mp hk

omit [Finite G] in
private theorem centralizes_disjoint_normal_factor_of_small_class
    [Finite G] (hc : _root_.commutator G ≤ center G)
    (V B : Subgroup G) [V.Normal] [B.Normal] (hVB : Disjoint V B)
    (t : G) (ht : (centralizer ({t} : Set G)).index ≤ 2)
    (hm : ¬ V ≤ centralizer ({t} : Set G)) :
    B ≤ centralizer ({t} : Set G) := by
  let D := ⁅zpowers t, (⊤ : Subgroup G)⁆
  let E := ⁅zpowers t, V⁆
  have hED : E ≤ D := commutator_mono le_rfl le_top
  have hD : Nat.card D ≤ 2 := by
    rw [← ClassTwo.centralizer_index hc t]
    exact ht
  have hEV : E ≤ V := commutator_le_right _ _
  have hEne : E ≠ ⊥ := by
    intro hh
    apply hm
    have htv := commutator_eq_bot_iff_le_centralizer.mp hh
    intro v hv
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (htv (mem_zpowers t)) v hv)
  have hEcard : 2 ≤ Nat.card E := by
    have hp : 0 < Nat.card E := Nat.card_pos
    have hn : Nat.card E ≠ 1 := fun hh => hEne (card_eq_one.mp hh)
    omega
  have hDE : D = E := (eq_of_le_of_card_ge hED (hD.trans hEcard)).symm
  have hDB : ⁅zpowers t, B⁆ = ⊥ := by
    apply bot_unique
    exact (le_inf ((commutator_mono le_rfl le_top).trans (hDE.le.trans hEV))
      (commutator_le_right _ _)).trans (disjoint_iff.mp hVB).le
  have htb := commutator_eq_bot_iff_le_centralizer.mp hDB
  intro b hb
  exact mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (htb (mem_zpowers t)) b hb)

private theorem alternating_residual_action_surjective
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3))
    (eR : pResidual 2 G ≃* alternatingGroup (Fin 4)) :
    let V := (pResidual 2 G).pCoreIn 2
    let B := pCore 2 G ⊓ centralizer ((pResidual 2 G : Subgroup G) : Set G)
    ∃ φ : G →* Equiv.Perm (Fin 4), Function.Surjective φ ∧ φ.ker = B ∧
      V.map φ = Theory.SpecificGroups.SymmetricSix.DuadCalculation.core := by
  let R := pResidual 2 G
  let Q := pCore 2 G
  let V := R.pCoreIn 2
  let C := centralizer (R : Set G)
  let B := Q ⊓ C
  obtain ⟨φ, _, hker, hVφ, hinj⟩ := alternating_residual_action eR
  have hCtwo : IsPGroup 2 C := by
    let q := (QuotientGroup.mk' R).comp C.subtype
    apply (isPGroup_quotient_pResidual (G := G) 2).of_injective q
    apply (MonoidHom.ker_eq_bot_iff q).mp
    apply bot_unique
    intro c hc
    have hcR : (c : G) ∈ R := (QuotientGroup.eq_one_iff _).mp hc
    have hφc : φ (c : G) = 1 := MonoidHom.mem_ker.mp (hker.symm ▸ c.property)
    have hh := hinj (a₁ := ⟨c, hcR⟩) (a₂ := 1) (by
      change φ (c : G) = φ 1
      simpa only [map_one] using hφc)
    exact Subtype.ext (congrArg (fun r : R => (r : G)) hh)
  have hCQ : C ≤ Q := le_sSup ⟨inferInstance, hCtwo⟩
  have hφB : φ.ker = B := hker.trans (inf_eq_right.mpr hCQ).symm
  obtain ⟨hsplit, hd, _, hVcard, _, hBN, _, _⟩ := alternating_residual_core_split eR
  let := hBN
  let : V.Normal := by dsimp [V, R, pCoreIn]; infer_instance
  change Q = V ⊔ B at hsplit
  change Nat.card V = 4 at hVcard
  have hVB : B ≤ normalizer (V : Set G) := by
    rw [normalizer_eq_top]
    exact le_top
  have hQcard : Nat.card Q = 4 * Nat.card B := by
    rw [hsplit, card_sup_eq_mul_of_normalizes_of_disjoint V B hVB hd, hVcard]
  have hGcard : Nat.card G = 24 * Nat.card B := by
    have hh : Nat.card G = 6 * Nat.card Q := SymmetricThreeTwoCore.card_eq e
    rw [hQcard] at hh
    omega
  have hφcard : Nat.card φ.range = 24 := by
    have hh := φ.ker.index_mul_card
    rw [index_ker, hφB, hGcard] at hh
    have hp : 0 < Nat.card B := Nat.card_pos
    nlinarith
  refine ⟨φ, MonoidHom.range_eq_top.mp ?_, hφB, hVφ⟩
  apply eq_top_of_card_eq
  rw [hφcard, Nat.card_perm, Nat.card_fin]
  rfl

theorem local_product_of_alternating
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) (P : Sylow 2 G)
    (hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup G).subtype).Normal)
    (eR : pResidual 2 G ≃* alternatingGroup (Fin 4)) :
    Nonempty (G ≃* Equiv.Perm (Fin 4) ×
      ↥(pCore 2 G ⊓ centralizer ((pResidual 2 G : Subgroup G) : Set G))) := by
  let R := pResidual 2 G
  let Q := pCore 2 G
  let V := R.pCoreIn 2
  let B := Q ⊓ centralizer (R : Set G)
  obtain ⟨hsplit, hd, hVe, hVcard, hVC, hBN, hRQ, hQR⟩ :=
    alternating_residual_core_split eR
  let := hVe
  let := hBN
  let : V.Normal := by dsimp [V, R, pCoreIn]; infer_instance
  change Q = V ⊔ B at hsplit
  change Disjoint V B at hd
  change Nat.card V = 4 at hVcard
  have hQP : Q ≤ (P : Subgroup G) := pCore_isPGroup.le_sylow_of_normal P
  have hVQ : V ≤ Q := hsplit.symm ▸ le_sup_left
  have hVP : V ≤ (P : Subgroup G) := hVQ.trans hQP
  have hBP : B ≤ (P : Subgroup G) := inf_le_left.trans hQP
  have hVR : V ≤ R := pCoreIn_le 2 R
  have hQi : Q.relIndex (P : Subgroup G) = 2 := by
    have hh := relIndex_mul_index hQP
    rw [SymmetricThreeTwoCore.sylow_index_three e P,
      SymmetricThreeTwoCore.core_index e] at hh
    omega
  have hVne : V ≠ ⊥ := by
    intro hh
    rw [hh, card_bot] at hVcard
    omega
  obtain ⟨t, htQ, ht2, hti⟩ :=
    Theory.GroupTheory.SmallClassInvolutions.exists_outside_of_no_characteristic_normal
      P Q R V hQP hVQ hVne hVC hQi hQR (pResidual_sup_sylow_eq_top P) hP
  obtain ⟨φ, hφ, hker, hVφ⟩ := alternating_residual_action_surjective e eR
  change φ.ker = B at hker
  change V.map φ = _ at hVφ
  have hm : ¬ V.subgroupOf (P : Subgroup G) ≤ centralizer ({t} : Set P) := by
    intro hfix
    have hφt : φ (t : G) ∈ Theory.SpecificGroups.SymmetricSix.DuadCalculation.core := by
      rw [← Theory.SpecificGroups.SymmetricSix.DuadCalculation.centralizer_core]
      apply mem_centralizer_iff.mpr
      intro v hv
      rw [← hVφ] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      have hh := mem_centralizer_singleton_iff.mp
        (hfix (show (⟨w, hVP hw⟩ : P) ∈ V.subgroupOf (P : Subgroup G) from hw))
      simpa only [Subgroup.coe_mul, map_mul] using
        congrArg φ (congrArg (fun x : P => (x : G)) hh)
    rw [← hVφ] at hφt
    obtain ⟨v, hv, he⟩ := hφt
    have hk : v⁻¹ * (t : G) ∈ B := by
      rw [← hker]
      change φ (v⁻¹ * (t : G)) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    have hh := Q.mul_mem (hVQ hv) hk.1
    exact htQ (by simpa only [mul_inv_cancel_left] using hh)
  have hc := local_sylow_class_two_of_alternating P hP eR
  have hBD : Disjoint (V.subgroupOf (P : Subgroup G)) (B.subgroupOf (P : Subgroup G)) := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    exact Subtype.ext ((disjoint_iff.mp hd).le hx)
  have htB := centralizes_disjoint_normal_factor_of_small_class hc
    (V.subgroupOf (P : Subgroup G)) (B.subgroupOf (P : Subgroup G)) hBD t hti hm
  let S := R ⊔ zpowers (t : G)
  have hSC : S ≤ centralizer (B : Set G) := by
    apply sup_le
    · exact le_centralizer_iff.mp (show B ≤ centralizer (R : Set G) from inf_le_right)
    · apply zpowers_le.mpr
      rw [mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp
        (htB (show (⟨b, hBP hb⟩ : P) ∈ B.subgroupOf (P : Subgroup G) from hb)))
  have hPgen : Q ⊔ zpowers (t : G) = (P : Subgroup G) := by
    apply le_antisymm (sup_le hQP (zpowers_le.mpr t.property))
    intro p hp
    by_cases hpQ : p ∈ Q
    · exact (show Q ≤ Q ⊔ zpowers (t : G) from le_sup_left) hpQ
    · have hpt : p * (t : G)⁻¹ ∈ Q := by
        have hh : (⟨p, hp⟩ : P) * t⁻¹ ∈ Q.subgroupOf (P : Subgroup G) := by
          rw [(Q.subgroupOf (P : Subgroup G)).mul_mem_iff_of_index_two hQi, inv_mem_iff]
          exact iff_of_false hpQ htQ
        exact hh
      have hh := (Q ⊔ zpowers (t : G)).mul_mem
        ((show Q ≤ Q ⊔ zpowers (t : G) from le_sup_left) hpt)
        ((show zpowers (t : G) ≤ Q ⊔ zpowers (t : G) from le_sup_right)
          (mem_zpowers (t : G)))
      simpa only [inv_mul_cancel_right] using hh
  have hgen : S ⊔ B = ⊤ := by
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top P]
    apply sup_le (le_sup_left.trans le_sup_left)
    rw [← hPgen, hsplit]
    exact sup_le (sup_le (hVR.trans (le_sup_left.trans le_sup_left)) le_sup_right)
      (le_sup_right.trans le_sup_left)
  have hRcard : Nat.card R = 12 := (Nat.card_congr eR.toEquiv).trans
    (alternatingGroup.card_of_card_eq_four (by simp))
  have htR : (t : G) ∉ R := by
    intro ht
    let U := V.subgroupOf R
    have hUcard : Nat.card U = 4 :=
      (Nat.card_congr (subgroupOfEquivOfLe hVR).toEquiv).trans hVcard
    have hquot : Nat.card (R ⧸ U) = 3 := by
      have hh := U.index_mul_card
      rw [hUcard, hRcard, index_eq_card] at hh
      omega
    let z : R := ⟨t, ht⟩
    let q := QuotientGroup.mk' U
    have htwo : q z ^ 2 = 1 := by
      rw [← map_pow]
      have hz : z ^ 2 = 1 := Subtype.ext (congrArg (fun x : P => (x : G)) ht2)
      rw [hz, map_one]
    have hthree : q z ^ 3 = 1 := hquot ▸ pow_card_eq_one'
    have hz : q z = 1 := by
      simpa only [pow_succ, pow_zero, one_mul, htwo] using hthree
    exact htQ (hVQ ((QuotientGroup.eq_one_iff z).mp hz))
  have hScard : Nat.card S = 24 := by
    change Nat.card (R ⊔ zpowers (t : G) : Subgroup G) = 24
    rw [card_sup_zpowers_of_normalizing_involution R (t : G)
      (congrArg (fun x : P => (x : G)) ht2) htR
      (by rw [normalizer_eq_top]; trivial), hRcard]
  let f : S →* Equiv.Perm (Fin 4) := φ.comp S.subtype
  have hfs : Function.Surjective f := by
    have hm := congrArg (map φ) hgen
    have hBφ : B.map φ = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hker.symm.le
    rw [Subgroup.map_sup, hBφ, sup_bot_eq, map_top_of_surjective φ hφ] at hm
    apply MonoidHom.range_eq_top.mp
    simpa only [f, MonoidHom.range_comp, range_subtype] using hm
  have hfcard : Nat.card S = Nat.card (Equiv.Perm (Fin 4)) := by
    rw [hScard, Nat.card_perm, Nat.card_fin]
    rfl
  have hf := (Nat.bijective_iff_surjective_and_card f).mpr ⟨hfs, hfcard⟩
  let eS := MulEquiv.ofBijective f hf
  have hSB : Disjoint S B := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have he : f (⟨x, hx.1⟩ : S) = f 1 := by
      change φ x = φ 1
      rw [map_one]
      exact MonoidHom.mem_ker.mp (hker.symm ▸ hx.2)
    exact congrArg Subtype.val (hf.1 he)
  obtain ⟨prod, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting S B hSB hSC
  exact ⟨((prod.trans ((MulEquiv.subgroupCongr hgen).trans topEquiv)).symm).trans
    (MulEquiv.prodCongr eS (MulEquiv.refl B))⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
