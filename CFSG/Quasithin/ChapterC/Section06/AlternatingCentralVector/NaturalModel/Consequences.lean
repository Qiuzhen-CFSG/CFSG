module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.NaturalModel.Coordinates
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.StructuralInput
public import Theory.GroupTheory.CentralizerRankMinimum.TwoCommutator
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The marked commutator line and the C.6.3 geometric input

The transposition image of R gives the literal ambient equality
[U,R]=⟨e₀₁⟩. This line has order two, so the centralizer-rank minimum is
one. S normalizes both factors of the commutator and therefore fixes the
unique nonidentity vector. The final application discharges the geometric
premise of the original C.6.3 factorization, retaining its separate index
premise; it does not assert centrality under Λ.

Source: Aschbacher–Smith C.6.3(3)(b), C.6.4(1),(10), pp.167–169.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
open BinaryPermutation.SevenMarkedAction
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

omit [Finite G] in
theorem Input.quotientMap_R_cases (d : Input K R S Λ) (r : R) :
    d.quotientMap (inclusion (d.R_le_S.trans le_sup_right) r) = 1 ∨
      d.quotientMap (inclusion (d.R_le_S.trans le_sup_right) r) = Equiv.swap 0 1 := by
  have hr : d.quotientMap (inclusion (d.R_le_S.trans le_sup_right) r) ∈
      zpowers (Equiv.swap (0 : Fin 7) 1) := by
    rw [← d.transposition]
    exact mem_map_of_mem _ r.property
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,
    show orderOf (Equiv.swap (0 : Fin 7) 1) = 2 from orderOf_eq_prime (by decide) (by decide)] at hr
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hr
  have hn' : n < 2 := Finset.mem_range.mp hn
  interval_cases n
  · exact Or.inl (by simpa using he.symm)
  · exact Or.inr (by simpa using he.symm)

omit [Finite G] in
/-- C.6.4(1), with the marked line in the original ambient group. -/
theorem Input.commutator_eq_marked_line (d : Input K R S Λ)
    (e : (blockU K).map K.subtype ≃* Multiplicative (core (Fin 7)))
    (he : ∀ (h : (K ⊔ S : Subgroup G)) (v : (blockU K).map K.subtype),
      (e.symm (Multiplicative.ofAdd (coreRepresentation (Fin 7)
        (d.quotientMap h) (e v).toAdd)) : G) = (h : G) * (v : G) * (h : G)⁻¹) :
    ⁅(blockU K).map K.subtype,R⁆ =
      (zpowers (e.symm (Multiplicative.ofAdd pairVector))).map
        ((blockU K).map K.subtype).subtype := by
  let U := (blockU K).map K.subtype
  let f : Multiplicative (core (Fin 7)) →* G := U.subtype.comp e.symm.toMonoidHom
  have hf : (zpowers (e.symm (Multiplicative.ofAdd pairVector))).map U.subtype =
      (zpowers (Multiplicative.ofAdd pairVector)).map f := by
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  rw [commutator_comm, hf]
  have hcomm (r : R) (v : U) :
      ⁅(r : G),(v : G)⁆ = f (Multiplicative.ofAdd
        (coreRepresentation (Fin 7)
          (d.quotientMap (inclusion (d.R_le_S.trans le_sup_right) r)) (e v).toAdd - (e v).toAdd)) := by
    rw [sub_eq_add_neg]
    change _ = (e.symm (Multiplicative.ofAdd
      (coreRepresentation (Fin 7) _ (e v).toAdd) * (e v)⁻¹) : G)
    rw [map_mul,map_inv,coe_mul,coe_inv,e.symm_apply_apply,he]
    rfl
  apply le_antisymm
  · apply commutator_le.mpr
    intro r hr u hu
    rw [hcomm ⟨r,hr⟩ ⟨u,hu⟩]
    apply mem_map_of_mem
    rcases d.quotientMap_R_cases ⟨r,hr⟩ with h | h
    · rw [h,map_one,Module.End.one_apply,sub_self]
      exact one_mem _
    · rw [h]
      exact swap_difference_mem _
  · rw [MonoidHom.map_zpowers]
    apply zpowers_le.mpr
    have ht : Equiv.swap (0 : Fin 7) 1 ∈ (R.subgroupOf (K ⊔ S)).map d.quotientMap :=
      d.transposition.symm ▸ mem_zpowers _
    obtain ⟨r,hr,hrt⟩ := ht
    obtain ⟨v,hv⟩ := swap_difference_nonzero
    let r₀ : R := ⟨r,hr⟩
    have hh := hcomm r₀ (e.symm (Multiplicative.ofAdd v))
    rw [e.apply_symm_apply] at hh
    change ⁅(r : G), (e.symm (Multiplicative.ofAdd v) : G)⁆ =
      f (Multiplicative.ofAdd (coreRepresentation (Fin 7) (d.quotientMap r) v - v)) at hh
    rw [hrt,hv] at hh
    rw [← hh]
    exact commutator_mem_commutator hr (e.symm (Multiplicative.ofAdd v)).property

/-- The commutator in C.6.4(1) has exactly two elements. -/
theorem Input.commutator_card (d : Input K R S Λ) :
    Nat.card (⁅(blockU K).map K.subtype,R⁆ : Subgroup G) = 2 := by
  obtain ⟨e,he⟩ := d.exists_marked_coordinates
  rw [d.commutator_eq_marked_line e he, card_map_of_injective
    ((blockU K).map K.subtype).subtype_injective, Nat.card_zpowers,
    e.symm.orderOf_eq]
  exact pairVector_order

/-- The geometric minimum in C.6.3(b), proved from the marked action. -/
theorem Input.centralizer_rank_minimum (d : Input K R S Λ) :
    let := d.block.2.1.elementary.map K.subtype
    centralizerRankMinimum R ((blockU K).map K.subtype) = 1 := by
  let := d.block.2.1.elementary.map K.subtype
  have hc : Nat.card (⁅R,(blockU K).map K.subtype⁆ : Subgroup G) = 2 := by
    rw [commutator_comm]
    exact d.commutator_card
  have hC : R ⊓ centralizer ((blockU K).map K.subtype : Set G) < R := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro he
    have hz : ⁅R,(blockU K).map K.subtype⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (he.symm ▸ inf_le_right)
    simp only [hz,Subgroup.card_bot] at hc
    omega
  exact centralizerRankMinimum_eq_one_of_commutator_card_le_two R _
    ((d.R_le_S.trans le_sup_right).trans d.normalizes_module) hC hc.le

/-- The S-part of C.6.4(10): S fixes the unique nonidentity commutator. -/
theorem Input.commutator_centralizes_S (d : Input K R S Λ) :
    ⁅(blockU K).map K.subtype,R⁆ ≤ centralizer (S : Set G) := by
  obtain ⟨e,he⟩ := d.exists_marked_coordinates
  let U := (blockU K).map K.subtype
  let z : G := e.symm (Multiplicative.ofAdd pairVector)
  have hline : ⁅U,R⁆ = zpowers z := by
    rw [d.commutator_eq_marked_line e he,MonoidHom.map_zpowers]
    rfl
  have hz : orderOf z = 2 := by
    change orderOf (U.subtype (e.symm (Multiplicative.ofAdd pairVector))) = 2
    rw [orderOf_injective U.subtype U.subtype_injective,
      e.symm.orderOf_eq]
    exact pairVector_order
  have hn : S ≤ normalizer (⁅U,R⁆ : Subgroup G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (d.normalizes_module ((show S ≤ K ⊔ S from le_sup_right) hs)),
      mem_normalizer_iff_map_conj_eq.mp (d.S_normalizes_R hs)]
  rw [hline,normalizer_zpowers_eq_centralizer_of_order_two z hz] at hn
  rw [hline]
  apply zpowers_le.mpr
  intro s hs
  exact (hn hs z (Set.mem_singleton z)).symm

/-- C.6.3 on the original marked input: its geometric premise is now discharged.
The index premise belongs to the subsequent C.6.4 escape and pair argument. -/
theorem Input.structural_factorization_of_index (d : Input K R S Λ)
    (hi : (S ⊓ Λ).relIndex (Λ ⊓ normalizer (R : Set G)) = 2) :
    let U := (blockU K).map K.subtype
    let Q := (K ⊔ S).pCoreIn 2
    let D := R ⊓ centralizer (K : Set G)
    ∃ x ∈ (Λ ⊓ normalizer (R : Set G)) ⊔ S,
      ¬ U.map (MulAut.conj x⁻¹ : G →* G) ≤ Q ∧
      R = U.map (MulAut.conj x⁻¹ : G →* G) ⊔ Q ∧
      Q = U ⊔ (Q ⊓ centralizer (U.map (MulAut.conj x⁻¹ : G →* G) : Set G)) ∧
      R = (U ⊔ U.map (MulAut.conj x⁻¹ : G →* G)) ⊔
        (R ⊓ centralizer ((U ⊔ U.map (MulAut.conj x⁻¹ : G →* G) : Subgroup G) : Set G)) ∧
      D ⊓ D.map (MulAut.conj x⁻¹ : G →* G) = ⊥ ∧
      frattini D = ⊥ ∧ IsElementaryAbelian 2 Q ∧
      R = Q ⊔ Q.map (MulAut.conj x⁻¹ : G →* G) :=
  d.structural_factorization hi d.centralizer_rank_minimum

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
