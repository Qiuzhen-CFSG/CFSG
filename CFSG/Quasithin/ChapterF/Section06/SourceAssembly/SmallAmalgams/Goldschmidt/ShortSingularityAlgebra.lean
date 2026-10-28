module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LargeLocalOrders
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralCoreIndex
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallResidualNormalizerAt
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Theory.GroupTheory.InvertedCubicSection
public import Theory.GroupTheory.SymmetricThreeQuotientInverter
public import Theory.GroupTheory.CharacteristicTwoIndexTwoRestriction

/-!
# The finite local contradiction for a singular three-arc

Let the same subgroup C, normal in the first endpoint group, be the
intersection of the two local two-cores and have index at most two in each.
If every involution in the opposite core lay in C, their first omega
subgroups would coincide and be normal at both endpoints, contradicting
primitive faithfulness. The resulting outside involution inverts a cubic
subgroup of the first endpoint group.

The literal join of that cubic subgroup and the opposite core has S₃
quotient and the opposite core as Sylow two-subgroup. Goldschmidt (2.15),
with all its hypotheses supplied by the actual amalgam, makes its Sylow
three-subgroups normal. The cubic therefore centralizes C. An odd-order
element centralizing an index-at-most-two subgroup of a self-centralizing
two-core is trivial, giving the contradiction.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (4.4),
printed p.393. Choosing the involution through the two characteristic
omega descriptions preserves the orientation supplied by the singular
three-arc and needs no finiteness assertion about its whole fixed subtree.
-/

public section
open Subgroup Theory.GroupTheory Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem omega_eq_of_involutions_le {C R : Subgroup G} (hCR : C ≤ R)
    (h : ∀ x ∈ R, x ^ 2 = 1 → x ∈ C) : omegaOneAmbient R = omegaOneAmbient C := by
  apply le_antisymm ?_ (omegaOneAmbient_mono hCR)
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro x hx hx2
  exact (omegaOneAmbient_le_iff C (omegaOneAmbient C)).mp le_rfl x (h x hx hx2) hx2
private theorem select_involution (h : CubicTreeAction F) (i : Bool) (C R : Subgroup G)
    (hCE : C ≤ F false ⊓ F true) (hCR : C ≤ R)
    (hCN : F i ≤ normalizer (C : Set G))
    (hRN : F (!i) ≤ normalizer (R : Set G))
    [Finite R] (hR2 : IsPGroup 2 R) (hRne : R ≠ ⊥) :
    ∃ t : G, t ∈ R ∧ orderOf t = 2 ∧ t ∉ C := by
  by_contra! hno
  have hOmega : omegaOneAmbient R = omegaOneAmbient C := by
    apply omega_eq_of_involutions_le hCR
    intro t ht ht2
    by_cases ht1 : t = 1
    · simp [ht1]
    · exact hno t ht (orderOf_eq_prime ht2 ht1)
  let : (omega₁ C (p := 2)).Characteristic := omega₁_characteristic C
  let : (omega₁ R (p := 2)).Characteristic := omega₁_characteristic R
  have hN1 : F i ≤ normalizer (omegaOneAmbient C : Set G) :=
    hCN.trans (normalizer_le_normalizer_characteristic_image C (omega₁ C (p := 2)))
  have hN2 : F (!i) ≤ normalizer (omegaOneAmbient C : Set G) := by
    rw [← hOmega]
    exact hRN.trans (normalizer_le_normalizer_characteristic_image R (omega₁ R (p := 2)))
  have ht : (⊤ : Subgroup G) ≤ normalizer (omegaOneAmbient C : Set G) := by
    have hp : F i ⊔ F (!i) = F false ⊔ F true := by cases i <;> simp [sup_comm]
    rw [← h.generated, ← hp]
    exact sup_le hN1 hN2
  let : (omegaOneAmbient C).Normal := normalizer_eq_top_iff.mp (top_unique ht)
  have hbot : omegaOneAmbient C = ⊥ :=
    bot_unique ((normal_le_normalCore.mpr ((omegaOneAmbient_le C).trans hCE)).trans
      h.common_core_eq_bot.le)
  have hd : 2 ∣ Nat.card R := by
    rcases hR2.card_eq_or_dvd with h1 | hd
    · exact (hRne (Subgroup.card_eq_one.mp h1)).elim
    · exact hd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 hd
  have htm : (t : G) ∈ omegaOneAmbient R :=
    (omegaOneAmbient_le_iff R (omegaOneAmbient R)).mp le_rfl t t.property
      (congrArg Subtype.val (ht ▸ pow_orderOf_eq_one t))
  rw [hOmega, hbot, mem_bot] at htm
  have h1 : t = 1 := Subtype.ext htm
  simp [h1] at ht

private theorem normal_three_intrinsic (h : CubicTreeAction F) (i : Bool) (J : Subgroup (F i)) (P : Sylow 2 J)
    (hPT : ((P : Subgroup J).map J.subtype).map (F i).subtype ≤ F false ⊓ F true)
    (hBN : F (!i) ≤ normalizer (((P : Subgroup J).map J.subtype).map (F i).subtype : Set G))
    (e : (J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) :
    ∀ S : Sylow 3 J, S.Normal := by
  let : Finite (F i) := h.finite i
  let H := J.map (F i).subtype
  let f : J ≃* H := J.equivMapOfInjective (F i).subtype (F i).subtype_injective
  let P' := P.mapSurjective (f := f.toMonoidHom) f.surjective
  have hp : (P' : Subgroup H).map H.subtype =
      ((P : Subgroup J).map J.subtype).map (F i).subtype := by
    change ((P : Subgroup J).map f.toMonoidHom).map H.subtype = _
    rw [map_map, map_map]
    rfl
  let e' : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.congr _ _ f.symm (pCore_map_iso 2 f.symm)).trans e
  have hall := h.normal_three_of_opposite_normalized_sylow_at i H (map_subtype_le J)
    P' (hp ▸ hPT) (hp ▸ hBN) e'
  intro S
  have hn : ((S : Subgroup J).map f.toMonoidHom).Normal :=
    hall (S.mapSurjective (f := f.toMonoidHom) f.surjective)
  exact Subgroup.Normal.of_map_injective (φ := f.toMonoidHom) f.injective hn
private theorem cubic_centralizes_normal_two {A : Type*} [Group A] [Finite A] (C : Subgroup A) [C.Normal] (hC : IsPGroup 2 C)
    (hn : ∀ S : Sylow 3 A, S.Normal) (x : A) (hx : orderOf x = 3) :
    x ∈ centralizer (C : Set A) := by
  have hX : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; rfl)
  obtain ⟨S, hS⟩ := hX.exists_le_sylow
  let : (S : Subgroup A).Normal := hn S
  have hd : Disjoint (S : Subgroup A) C := S.isPGroup'.disjoint_of_coprime hC (by decide)
  exact (commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd))
    (hS (mem_zpowers x))

private theorem no_cubic_fixed_core {A : Type*} [Group A] [Finite A]
    (hcent : centralizer (pCore 2 A : Set A) ≤ pCore 2 A)
    (C : Subgroup A) (hi : C.relIndex (pCore 2 A) ≤ 2)
    (x : A) (hx : orderOf x = 3) (hxc : x ∈ centralizer (C : Set A)) : False := by
  have hpos : C.relIndex (pCore 2 A) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcases : C.relIndex (pCore 2 A) = 1 ∨ C.relIndex (pCore 2 A) = 2 := by omega
  have hp : IsPGroup 2 (centralizer (C : Set A)) := by
    rcases hcases with h1 | h2
    · exact pCore_isPGroup.to_le ((centralizer_le (Subgroup.relIndex_eq_one.mp h1)).trans hcent)
    · exact centralizer_isPGroup_of_index_two_in_core hcent C h2
  have hh := hp.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨x, hxc⟩ : centralizer (C : Set A))
  rw [Subgroup.orderOf_mk, hx] at hh
  norm_num at hh
/-- The two small kernel indices contradict the large local residual branch.
The kernel is normal in the prescribed first endpoint, and both indices
refer to that same kernel. All finite-section and cubic normality inputs
are constructed from the actual source action. -/
theorem CubicTreeAction.false_of_short_core_intersection (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (i : Bool) (C : Subgroup G)
    (hCeq : C = (F i).pCoreIn 2 ⊓ (F (!i)).pCoreIn 2)
    (hCN : F i ≤ normalizer (C : Set G))
    (hiA : C.relIndex ((F i).pCoreIn 2) ≤ 2)
    (hiB : C.relIndex ((F (!i)).pCoreIn 2) ≤ 2) : False := by
  let A := F i
  let B := F (!i)
  let R := B.pCoreIn 2
  let : Finite A := h.finite i
  let : Finite B := h.finite (!i)
  have hRE : R ≤ F false ⊓ F true := by
    have hadj : (RankTwo.graph F).Adj (base F i) (base F (!i)) :=
      ⟨by change i ≠ !i; cases i <;> decide, incident_base F i (!i)⟩
    have hh := h.vertexTwoCore_le_edge hadj
    rw [show RankTwo.stabilizer F (base F i) = A from stabilizer_base F i,
      show RankTwo.stabilizer F (base F (!i)) = B from stabilizer_base F (!i)] at hh
    have he : A ⊓ B = F false ⊓ F true := by cases i <;> simp [A, B, inf_comm]
    exact hh.trans_eq he
  have hRA : R ≤ A := hRE.trans (by cases i; exact inf_le_left; exact inf_le_right)
  let : Finite R := Finite.of_injective (inclusion (pCoreIn_le 2 B)) (inclusion_injective _)
  have hR2 : IsPGroup 2 R := isPGroup_pCoreIn 2 B
  have hCR : C ≤ R := by rw [hCeq]; exact inf_le_right
  have hCA : C ≤ A := hCR.trans hRA
  have hRne : R ≠ ⊥ := by
    intro hb
    have hcR : Nat.card R = Nat.card (pCore 2 B) := card_map_of_injective B.subtype_injective
    have hcard := h.local_card_gt_twentyFour_of_large_residual hC hA (!i)
    obtain ⟨eB⟩ := h.local_quotient_symmetricThree_of_large_residual hC hA (!i)
    have hh := SymmetricThreeTwoCore.card_eq eB
    rw [hb, card_bot] at hcR
    change 24 < Nat.card B at hcard
    change Nat.card B = 6 * Nat.card (pCore 2 B) at hh
    omega
  have hRN : B ≤ normalizer (R : Set G) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  obtain ⟨t, htR, ht2, htC⟩ := select_involution h i C R (hCR.trans hRE) hCR hCN hRN hR2 hRne
  have htA : t ∈ A := hRA htR
  have htQ : (⟨t, htA⟩ : A) ∉ pCore 2 A := by
    intro ht
    apply htC
    rw [hCeq]
    exact ⟨mem_map_of_mem A.subtype ht, htR⟩
  let tA : A := ⟨t, htA⟩
  obtain ⟨X, hX, hinv⟩ := exists_inverted_three_of_symmetric_three_quotient
    (pCore 2 A) pCore_isPGroup (h.local_quotient_symmetricThree_of_large_residual hC hA i)
    tA ((orderOf_coe tA).symm.trans ht2) htQ
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hX])
  let xA : A := x
  have hx3 : orderOf xA = 3 := (orderOf_coe x).trans hx
  let C' := C.subgroupOf A
  let R' := R.subgroupOf A
  let : C'.Normal := (normal_subgroupOf_iff_le_normalizer hCA).mpr hCN
  have hiR : C'.relIndex R' = 2 := by
    rw [relIndex_subgroupOf hRA]
    have hn0 : C.relIndex R ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hn1 : C.relIndex R ≠ 1 := fun h1 => htC (relIndex_eq_one.mp h1 htR)
    change C.relIndex R ≤ 2 at hiB
    omega
  obtain ⟨P, hP, ⟨e⟩⟩ := sylow_and_quotient_of_index_two_inverted_cubic C' R' (fun _ hx => hCR hx) hR2.comap_subtype hiR
    tA xA htR (by apply Subtype.ext; exact ht2 ▸ pow_orderOf_eq_one t) htC hx3 (hinv x x.property)
  let J := R' ⊔ zpowers xA
  have hpImage : ((P : Subgroup J).map J.subtype).map A.subtype = R := by
    rw [hP, map_subgroupOf_eq_of_le hRA]
  have hall := normal_three_intrinsic h i J P (hpImage ▸ hRE) (hpImage ▸ hRN) e
  have hCJ : C' ≤ J := (show C' ≤ R' from fun _ hx => hCR hx).trans le_sup_left
  let CJ := C'.subgroupOf J
  let xJ : J := ⟨xA, mem_sup_right (mem_zpowers xA)⟩
  have hxCJ := cubic_centralizes_normal_two CJ (hR2.comap_subtype.to_le
    (show C' ≤ R' from fun _ hx => hCR hx)).comap_subtype hall xJ
      ((orderOf_coe xJ).symm.trans hx3)
  have hxCent : xA ∈ centralizer (C' : Set A) := by
    intro c hc
    exact congrArg Subtype.val (hxCJ ⟨c, hCJ hc⟩ hc)
  have hQi : C'.relIndex (pCore 2 A) ≤ 2 := by
    have hc := relIndex_map_map_of_injective C' (pCore 2 A) A.subtype_injective
    rw [map_subgroupOf_eq_of_le hCA] at hc
    exact hc ▸ hiA
  have hcent := h.stabilizer_centralizer_twoCore_le_of_large_residual hC hA (base F i)
  rw [show RankTwo.stabilizer F (base F i) = A from stabilizer_base F i] at hcent
  exact no_cubic_fixed_core hcent C' hQi xA hx3 hxCent
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
