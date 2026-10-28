module

public import Stellmacher.Recognition.NormalEightSeparatedClosureEightLocalData
public import Theory.GroupTheory.PGroup.UniqueCentralInvolutionNormal
public import Theory.GroupTheory.PGroup.NormalEightCentralizerCharacteristic
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.IndexTwoIntersection

/-!
# The fixed factor in the order-eight local splitting

The fixed factor of the supplied splitting has order two. Intersecting the
closure centralizer with its outside conjugate gives a normal subgroup U of
index two in that centralizer. The elementary closure supplements U centrally,
so their derived subgroups agree with the derived subgroup of the fixed factor.
Normality and avoidance of the unique central involution make this derived
subgroup trivial.

The fixed factor is consequently central in the involution centralizer. Squares
of its center lie in the fixed factor and form a normal subgroup of the Sylow
group, so the same central-involution argument kills them. The central omega
four then contains the fixed factor, which contains i and avoids z.

This is Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, printed p.388,
paragraphs beginning “Assume that B′ ≠ 1” and “We have proved that B is abelian.”
Source: refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedClosureEight
open Subgroup NormalEightSeparatedCentralizers
open scoped IsMulCommutative commutatorElement Pointwise

section
variable {P : Type*} [Group P]

private theorem map_centralizer (E : Subgroup P) (f : P ≃* P) :
    (centralizer (E : Set P)).map f.toMonoidHom = centralizer (E.map f.toMonoidHom : Set P) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    intro y hy
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using hx (f y) (mem_map_of_mem _ hy)

private theorem centralizer_join (E F : Subgroup P) :
    centralizer (E ⊔ F : Subgroup P) = centralizer (E : Set P) ⊓ centralizer (F : Set P) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (show E ≤ E ⊔ F from le_sup_left))
      (centralizer_le (show F ≤ E ⊔ F from le_sup_right))
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)

private theorem commutator_central_join (A B : Subgroup P)
    (hA : A ≤ centralizer (A ⊔ B : Subgroup P)) :
    ⁅A ⊔ B, A ⊔ B⁆ = ⁅B, B⁆ := by
  have hBA : B ≤ centralizer (A : Set P) :=
    le_centralizer_iff.mp (hA.trans (centralizer_le (show B ≤ A ⊔ B from le_sup_right)))
  have hnorm : B ≤ normalizer (A : Set P) := hBA.trans (centralizer_le_normalizer _)
  have hprod (x : P) (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
    have hh : x ∈ (A : Set P) * (B : Set P) := by
      rw [← coe_mul_of_right_le_normalizer_left A B hnorm]
      exact hx
    exact hh
  apply le_antisymm ?_ (commutator_mono le_sup_right le_sup_right)
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
  obtain ⟨c, hc, d, hd, rfl⟩ := hprod y hy
  have hab : Commute a b := (hA ha b (mem_sup_right hb)).symm
  have hac : Commute a c := (hA ha c (mem_sup_left hc)).symm
  have had : Commute a d := (hA ha d (mem_sup_right hd)).symm
  have hcb : Commute c b := (hA hc b (mem_sup_right hb)).symm
  have hcd : Commute c d := (hA hc d (mem_sup_right hd)).symm
  have heq : ⁅a*b,c*d⁆ = ⁅b,d⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul,
      (hac.mul_right had).commutator_eq]
    rw [commutatorElement_mul_right_eq_mul_conj, hcb.symm.commutator_eq]
    have hcomm : Commute c ⁅b,d⁆ := hcb.mul_right hcd |>.mul_right hcb.inv_right |>.mul_right hcd.inv_right
    have hcomm' : Commute a ⁅b,d⁆ := hab.mul_right had |>.mul_right hab.inv_right |>.mul_right had.inv_right
    simp only [one_mul, hcomm.eq, hcomm'.eq, mul_inv_cancel_right, mul_one]
  rw [heq]
  exact commutator_mem_commutator hb hd


end

variable {G : Type*} [Group G] [Finite G]

private theorem fixed_derived_normal
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2) (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (d : CentralizerSetup S W i) (hc : Nat.card d.closure = 8)
    (s : LocalSplitting d z) : (⁅s.fixed, s.fixed⁆).Normal := by
  let E := closureInSylow d
  let F := E.map (MulAut.conj s.mover).toMonoidHom
  let C := centralizer ({i} : Set S)
  let T := centralizer (E : Set S)
  let T' := centralizer (F : Set S)
  let U := T ⊓ T'
  have hC : C.index = 2 := centralizer_involution_index S W hW z hzW hzC hz i hiW hi hiC
  let : C.Normal := normal_of_index_eq_two hC
  have hn : normalizer (E : Set S) = C :=
    normalizer_closureInSylow_eq S W hW z hzW hzC hz i hiW hi hiC hno d hc
  have hTC : T ≤ C := (centralizer_le_normalizer _).trans_eq hn
  have hCmap : C.map (MulAut.conj s.mover).toMonoidHom = C :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [C.normalizer_eq_top]; trivial)
  have hTmap : T.map (MulAut.conj s.mover).toMonoidHom = T' := map_centralizer _ _
  have hT'C : T' ≤ C := by
    rw [← hTmap, ← hCmap]
    exact map_mono hTC
  have hT'index : T'.relIndex C = 2 := by
    rw [← hTmap, ← hCmap, relIndex_map_map_of_injective _ _ (MulAut.conj s.mover).injective]
    exact s.index
  let : IsElementaryAbelian 2 E := closureInSylow_elementary d
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map _
  have hET : E ≤ T := le_centralizer E
  have hFT' : F ≤ T' := le_centralizer F
  have hnot : ¬ T ≤ T' := by
    intro h
    have hcards : Nat.card T' = Nat.card T := by
      rw [← hTmap]
      exact card_map_of_injective (MulAut.conj s.mover).injective
    have heq : T = T' := eq_of_le_of_card_ge h hcards.le
    exact s.outside_not_centralizing (heq.ge (hFT' s.outside_mem_conjugate))
  have hUindex : U.relIndex T = 2 := by
    have hnle : ¬ T.subgroupOf C ≤ T'.subgroupOf C := by
      intro h
      exact hnot fun x hx => h (show (⟨x,hTC hx⟩ : C) ∈ T.subgroupOf C from hx)
    have hh := subgroupOf_index_eq_two (T'.subgroupOf C) (T.subgroupOf C) hT'index hnle
    change (T'.subgroupOf C).relIndex (T.subgroupOf C) = 2 at hh
    rw [relIndex_subgroupOf hTC] at hh
    simpa only [U, inf_relIndex_left] using hh
  let : (E ⊔ F).Normal := sup_conjugate_normal_of_normalizer_index_two E
    (by rw [hn]; exact hC) s.mover (by rw [hn]; exact s.mover_outside)
  have hUeq : U = centralizer (E ⊔ F : Subgroup S) := (centralizer_join E F).symm
  have hUn : U.Normal := by rw [hUeq]; infer_instance
  let : U.Normal := hUn
  have hxU : s.outside ∈ centralizer (U : Set S) :=
    le_centralizer_iff.mp (show U ≤ centralizer (F : Set S) from inf_le_right)
      s.outside_mem_conjugate
  have hEnot : ¬ E ≤ U := by
    intro h
    exact s.outside_not_centralizing (centralizer_le h hxU)
  have hTU : E ⊔ U = T := by
    have hle : E ⊔ U ≤ T := sup_le hET inf_le_left
    have hd : (E ⊔ U).relIndex T ∣ 2 := by
      have hh : (E ⊔ U).relIndex T ∣ U.relIndex T := relIndex_dvd_of_le_left T le_sup_right
      simpa only [hUindex] using hh
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact le_antisymm hle (relIndex_eq_one.mp h)
    · have htower := relIndex_mul_relIndex U (E ⊔ U) T le_sup_right hle
      rw [h, hUindex] at htower
      have heq : U.relIndex (E ⊔ U) = 1 := by omega
      exact (hEnot (le_sup_left.trans (relIndex_eq_one.mp heq))).elim
  have hcommU : ⁅T,T⁆ = ⁅U,U⁆ := by
    rw [← hTU]
    apply commutator_central_join
    rw [hTU]
    exact le_centralizer_iff.mp le_rfl
  have hcommB : ⁅T,T⁆ = ⁅s.fixed,s.fixed⁆ := by
    change ⁅centralizer (closureInSylow d : Set S), centralizer (closureInSylow d : Set S)⁆ = _
    rw [← s.product]
    apply commutator_central_join
    rw [s.product]
    exact s.plane_le.trans (le_centralizer_iff.mp le_rfl)
  rw [← hcommB, hcommU]
  infer_instance


private theorem fixed_card_of_abelian
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2) (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (d : CentralizerSetup S W i) (s : LocalSplitting d z)
    (hB : IsMulCommutative s.fixed) : Nat.card s.fixed = 2 := by
  let : IsElementaryAbelian 2 s.plane := s.plane_elementary
  let E := closureInSylow d
  let C := centralizer ({i} : Set S)
  let T := centralizer (E : Set S)
  have hTC : T ≤ C := centralizer_le (Set.singleton_subset_iff.mpr
    (four_le_closureInSylow hiW d hiW))
  have hBC : s.fixed ≤ C := (le_sup_right.trans s.product.le).trans hTC
  have hBT : s.fixed ≤ T := le_sup_right.trans s.product.le
  have hBA : s.fixed ≤ centralizer (s.plane : Set S) :=
    hBT.trans (centralizer_le s.plane_le)
  let : IsMulCommutative s.fixed := hB
  have hBTc : s.fixed ≤ centralizer (T : Set S) := by
    apply le_centralizer_iff.mpr
    exact s.product.ge.trans (sup_le (le_centralizer_iff.mp hBA) (le_centralizer s.fixed))
  have hxC : s.outside ∈ C :=
    conjugate_closure_le_centralizer S W hW z hzW hzC hz i hiW hi hiC d s.mover
      s.outside_mem_conjugate
  have hBCc : s.fixed ≤ centralizer (C : Set S) := by
    apply le_centralizer_iff.mpr
    intro c hc
    by_cases hcT : c ∈ T
    · exact le_centralizer_iff.mp hBTc hcT
    · have hcx : c * s.outside⁻¹ ∈ T :=
        (T.subgroupOf C).mul_mem_iff_of_index_two s.index
          (a := ⟨c,hc⟩) (b := ⟨s.outside⁻¹,C.inv_mem hxC⟩) |>.mpr (by
            simpa only [mem_subgroupOf, inv_mem_iff] using
              iff_of_false hcT s.outside_not_centralizing)
      simpa using (centralizer (s.fixed : Set S)).mul_mem
        (le_centralizer_iff.mp hBTc hcx) s.outside_centralizes_fixed
  let ZC := (center C).map C.subtype
  have hBZ : s.fixed ≤ ZC := by
    intro b hb
    refine ⟨⟨b,hBC hb⟩, mem_center_iff.mpr ?_, rfl⟩
    intro c
    exact Subtype.ext (hBCc hb c c.property)
  have hZT : ZC ≤ T := by
    rintro b ⟨c, hc, rfl⟩ e he
    exact congrArg Subtype.val (mem_center_iff.mp hc ⟨e,closureInSylow_le_centralizer d he⟩)
  have hnorm : s.fixed ≤ normalizer (s.plane : Set S) :=
    hBA.trans (centralizer_le_normalizer _)
  have hsquare (c : center C) : ((c : C) : S) ^ 2 ∈ s.fixed := by
    have hcT := hZT (mem_map_of_mem C.subtype c.property)
    have hcprod : ((c : C) : S) ∈ (s.plane : Set S) * (s.fixed : Set S) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hnorm, s.product]
      exact hcT
    obtain ⟨a, ha, b, hb, heq⟩ := hcprod
    rw [← heq]
    have hab : Commute a b := hBA hb a ha
    rw [hab.mul_pow, elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := s.plane) a ha, one_mul]
    exact s.fixed.pow_mem hb 2
  let K := closure (Set.range (fun c : center C => c ^ 2))
  let : K.Characteristic := closure_range_pow_characteristic 2
  let L := K.map (center C).subtype
  let : L.Characteristic := characteristic_of_characteristic_of_characteristic
  have hC : C.index = 2 := centralizer_involution_index S W hW z hzW hzC hz i hiW hi hiC
  let : C.Normal := normal_of_index_eq_two hC
  let N := L.map C.subtype
  let : N.Normal := ConjAct.normal_of_characteristic_of_normal
  have hNB : N ≤ s.fixed := by
    rw [map_le_iff_le_comap, map_le_iff_le_comap]
    apply (closure_le _).mpr
    rintro _ ⟨c,rfl⟩
    exact hsquare c
  have hNbot : N = ⊥ := S.isPGroup'.normal_eq_bot_of_avoiding_unique_central_involution
    hZ z hzC hz N (fun h => s.central_not_mem_fixed (hNB h))
  have hBpow (b : S) (hb : b ∈ s.fixed) : b ^ 2 = 1 := by
    obtain ⟨c,hc,heq⟩ := hBZ hb
    have hmem : b ^ 2 ∈ N := by
      rw [← heq]
      exact mem_map_of_mem C.subtype
        (mem_map_of_mem (center C).subtype
          (show (⟨c,hc⟩ : center C)^2 ∈ K from
            subset_closure ⟨(⟨c,hc⟩ : center C),rfl⟩))
    rwa [hNbot, mem_bot] at hmem
  have hBW : s.fixed ≤ W := by
    have hfour := omega_one_center_centralizer_eq_normal_four hno W hW
    rw [← centralizer_involution_eq_four S W hW z hzW hzC hz i hiW hi hiC] at hfour
    intro b hb
    apply hfour.le
    obtain ⟨c,hc,heq⟩ := hBZ hb
    refine ⟨c, ⟨⟨c,hc⟩, subset_closure ?_, rfl⟩,heq⟩
    apply Subtype.ext
    apply Subtype.ext
    change (c : S) ^ 2 = 1
    change (c : S) = b at heq
    rw [heq]
    exact hBpow b hb
  have hlt : Nat.card s.fixed < 4 := by
    have hle := card_le_of_le hBW
    have hne : Nat.card s.fixed ≠ Nat.card W := by
      intro heq
      have he := eq_of_le_of_card_ge hBW heq.ge
      exact s.central_not_mem_fixed (he.symm ▸ hzW)
    omega
  have hd : 2 ∣ Nat.card s.fixed := by
    have h := card_dvd_of_le (zpowers_le.mpr s.involution_mem_fixed)
    rwa [Nat.card_zpowers, hi] at h
  have hp : 0 < Nat.card s.fixed := Nat.card_pos
  omega


/-- The fixed factor of the local splitting is precisely an involution line
in cardinality. No commutativity or exponent assumption on that factor is
needed: both follow from the unique central involution. -/
public theorem fixed_card_of_localSplitting
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2) (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (d : CentralizerSetup S W i) (hc : Nat.card d.closure = 8)
    (s : LocalSplitting d z) : Nat.card s.fixed = 2 := by
  let : (⁅s.fixed, s.fixed⁆).Normal :=
    fixed_derived_normal S W hW z hzW hzC hz i hiW hi hiC hno d hc s
  have hcomm : ⁅s.fixed, s.fixed⁆ = ⊥ :=
    S.isPGroup'.normal_eq_bot_of_avoiding_unique_central_involution hZ z hzC hz
      ⁅s.fixed, s.fixed⁆ (fun h => s.central_not_mem_fixed (commutator_le_self s.fixed h))
  exact fixed_card_of_abelian S W hW hZ z hzW hzC hz i hiW hi hiC hno d s
    (commutator_self_eq_bot_iff.mp hcomm)

end Stellmacher.Recognition.NormalEightSeparatedClosureEight
