module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicCentralizerDichotomy

/-!
# The binary octagon's irreducible five-root quotient

Every subgroup between the five middle roots J and the radical V that is
invariant under the actual rank-one actor and the full Cartan equals J or V.
The cubic actor's fixed-point congruence leaves indices one, four and sixteen;
the end-root argument excludes four. When J is parabolic-invariant, this
constructs the literal conjugation action on V/J and proves that it has no
proper nontrivial invariant subgroup. Normality is relative to V.

Source: Fong--Seitz I (1973), (6G), printed p.50, first paragraph. This is
the irreducibility assertion in the five-root centralizer alternative. The
original-factor and Chapter 12 applications discharge the local linear and
cubic premises. Excluding that alternative and completing the later
normalizer argument are still separate obligations.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem overgroup_index (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (hj : Nat.card (simpleRoot Q split j) = 4)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) (horder : orderOf c = 3)
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥)
    (C : Subgroup (X ⧸ Q.D))
    (hJC : middleFive Q split i j ≤ C) (hCV : C ≤ simpleRemainder Q split i)
    (hnc : (c : X ⧸ Q.D) ∈ normalizer (C : Set (X ⧸ Q.D))) :
    C.relIndex (simpleRemainder Q split i) = 1 ∨
    C.relIndex (simpleRemainder Q split i) = 4 ∨
    C.relIndex (simpleRemainder Q split i) = 16 := by
  let V := simpleRemainder Q split i
  have hfixV := (octagon_separated_root_centralizer_orders Q split hm i j hij c hc).1
  rw [hi] at hfixV
  have hfixle : V ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) ≤ C := by
    rw [←separated_radical_centralizer_sup Q split hm i j hij c hc]
    apply le_trans _ hJC
    exact sup_le (sup_le
      (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left)))
      (le_sup_of_le_left (le_sup_of_le_left le_sup_right))) le_sup_right
  have hfixC : C ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) =
      V ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :=
    le_antisymm (inf_le_inf_right _ hCV) (le_inf hfixle inf_le_right)
  have hp : IsPGroup 3 (zpowers (c : X ⧸ Q.D)) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,orderOf_coe,horder]; rfl)
  have hmod := card_modEq_card_inf_centralizer (zpowers (c : X ⧸ Q.D)) C hp
    (zpowers_le.mpr hnc)
  rw [zpowers_eq_closure,centralizer_closure,hfixC,hfixV] at hmod
  have hd : C.relIndex V ∣ 16 :=
    by
      rw [←binary_middleFive_quotient_card Q split hm i j hij hi hj]
      exact index_dvd_of_le (subgroupOf_mono _ hJC)
  have h16 : Nat.card V = 128*16 := by
    have hJ : Nat.card (middleFive Q split i j) = 128 := by
      rw [middleFive_card Q split hm i j hij,hi,hj]; norm_num
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D))
      (middleFive Q split i j) V bot_le (middleFive_le_remainder Q split hm i j hij)
    rw [relIndex_bot_left,relIndex_bot_left,hJ] at hh
    have hq := binary_middleFive_quotient_card Q split hm i j hij hi hj
    change (middleFive Q split i j).relIndex V = 16 at hq
    rw [hq] at hh
    exact hh.symm
  have hmC := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D)) C V bot_le hCV
  rw [relIndex_bot_left,relIndex_bot_left,h16] at hmC
  change Nat.card C % 3 = 8 % 3 at hmod
  have hle : C.relIndex V ≤ 16 := Nat.le_of_dvd (by decide) hd
  change C.relIndex V = 1 ∨ C.relIndex V = 4 ∨ C.relIndex V = 16
  interval_cases C.relIndex V <;> omega


/-- Invariant overgroups of the five middle roots have no intermediate size. -/
theorem separated_binary_middleFive_overgroup
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* PSL(2,F))
    (s : HexagonStructure.RootReflection Q split i)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (hj : Nat.card (simpleRoot Q split j) = 4)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) (horder : orderOf c = 3)
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥)
    (C : Subgroup (X ⧸ Q.D))
    (hJC : middleFive Q split i j ≤ C) (hCV : C ≤ simpleRemainder Q split i)
    (hRC : rankOne Q split i ≤ normalizer (C : Set (X ⧸ Q.D)))
    (hHC : Q.tits.B ⊓ Q.tits.N ≤ normalizer (C : Set (X ⧸ Q.D))) :
    C = middleFive Q split i j ∨ C = simpleRemainder Q split i := by
  have hEA := simpleRoot_elementary_of_linear Q split j μj
  let := hEA
  have hVC := middleFive_overgroup_normalized Q split hm i j hij hKj
    (commutator_self_eq_bot_iff.mpr inferInstance) C hJC hCV
  have hUC : split.U ≤ normalizer (C : Set (X ⧸ Q.D)) := by
    intro x hx
    have hp : x ∈ (simpleRoot Q split i : Set (X ⧸ Q.D))*
        (simpleRemainder Q split i : Set (X ⧸ Q.D)) :=
      (simpleRoot_mul_remainder Q split i).symm ▸ hx
    obtain ⟨a,ha,v,hv,rfl⟩ := hp
    exact mul_mem (hRC (mem_sup_left ha)) (hVC hv)
  have hBC : Q.tits.B ≤ normalizer (C : Set (X ⧸ Q.D)) := by
    rw [←split.factorization]
    exact sup_le hUC hHC
  have hPC : Q.tits.standardParabolic {Q.simple i} ≤ normalizer (C : Set (X ⧸ Q.D)) := by
    apply Q.tits.standardParabolic_le _ hBC
    intro w hw
    have hw' : w = Q.simple i := Set.mem_singleton_iff.mp hw
    subst w
    exact Q.tits.bruhatCell_subset_of_mem _ hBC
      (Q.tits.representative_mem_bruhatCell _ s.val s.class_eq) (hRC s.mem_rankOne)
  rcases overgroup_index Q split hm i j hij hi hj c horder hc C hJC hCV
    (hHC c.property) with h1 | h4 | h16
  · exact Or.inr (le_antisymm hCV (relIndex_eq_one.mp h1))
  · exact (binary_middle_overgroup_index_ne_four Q split hm i j hij hKi hKj μj s
      hi hj C hJC hCV hPC h4).elim
  · apply Or.inl
    have hq := binary_middleFive_quotient_card Q split hm i j hij hi hj
    change (middleFive Q split i j).relIndex (simpleRemainder Q split i) = 16 at hq
    have hh := relIndex_mul_relIndex (middleFive Q split i j) C
      (simpleRemainder Q split i) hJC hCV
    rw [h16,hq] at hh
    have he : (middleFive Q split i j).relIndex C = 1 := by omega
    exact le_antisymm (relIndex_eq_one.mp he) hJC

private theorem quotient_action_irreducible {Y : Type*} [Group Y]
    (A V J : Subgroup Y) (hJV : J ≤ V)
    [hn : (J.subgroupOf V).Normal]
    (hAV : A ≤ normalizer (V : Set Y))
    (hAJ : A ≤ normalizer (J : Set Y))
    (hmin : ∀ C : Subgroup Y, J ≤ C → C ≤ V → A ≤ normalizer (C : Set Y) →
      C = J ∨ C = V) :
    ∃ φ : A →* MulAut (V ⧸ J.subgroupOf V),
      (∀ (a : A) (v : V), φ a (QuotientGroup.mk v) =
        QuotientGroup.mk (V.normalizerMonoidHom (inclusion hAV a) v)) ∧
      ∀ D : Subgroup (V ⧸ J.subgroupOf V),
        (∀ a : A, ∀ x ∈ D, φ a x ∈ D) → D = ⊥ ∨ D = ⊤ := by
  let ψ := V.normalizerMonoidHom.comp (inclusion hAV)
  have hJ (a : A) : (J.subgroupOf V).map (ψ a).toMonoidHom = J.subgroupOf V := by
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      exact (mem_normalizer_iff.mp (hAJ a.property) (v : Y)).mp hv
    · intro v hv
      refine ⟨ψ a⁻¹ v,?_,?_⟩
      · exact (mem_normalizer_iff.mp (hAJ (inv_mem a.property)) (v : Y)).mp hv
      · change ψ a (ψ a⁻¹ v) = v
        rw [map_inv]
        exact (ψ a).apply_symm_apply v
  let φ := sectionQuotientAction ψ (J.subgroupOf V) hJ
  refine ⟨φ,fun a v => rfl,?_⟩
  intro D hD
  let C := (D.comap (QuotientGroup.mk' (J.subgroupOf V))).map V.subtype
  have hJC : J ≤ C := by
    intro x hx
    refine ⟨⟨x,hJV hx⟩,?_,rfl⟩
    change QuotientGroup.mk' (J.subgroupOf V) ⟨x,hJV hx⟩ ∈ D
    rw [show QuotientGroup.mk' (J.subgroupOf V) ⟨x,hJV hx⟩ = 1 from
      (QuotientGroup.eq_one_iff _).mpr hx]
    exact D.one_mem
  have hCV : C ≤ V := map_subtype_le _
  have hconj (a : A) {x : Y} (hx : x ∈ C) : (a : Y)*x*(a : Y)⁻¹ ∈ C := by
    obtain ⟨v,hv,rfl⟩ := hx
    refine ⟨ψ a v,?_,rfl⟩
    exact hD a (QuotientGroup.mk v) hv
  have hAC : A ≤ normalizer (C : Set Y) := by
    intro a ha
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · exact hconj ⟨a,ha⟩
    · intro hx
      have hh := hconj ⟨a⁻¹,inv_mem ha⟩ hx
      simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh
  rcases hmin C hJC hCV hAC with hC | hC
  · left
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (J.subgroupOf V) x
    have hv : (v : Y) ∈ C := mem_map_of_mem V.subtype hx
    rw [hC] at hv
    exact mem_bot.mpr ((QuotientGroup.eq_one_iff _).mpr hv)
  · right
    apply top_unique
    intro x _
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (J.subgroupOf V) x
    have hv : (v : Y) ∈ C := hC.symm ▸ v.property
    obtain ⟨w,hw,he⟩ := hv
    have he' : w = v := Subtype.ext he
    subst w
    exact hw

/-- The actual rank-one and full-Cartan conjugation action on the invariant
five-root quotient is irreducible. -/
theorem separated_binary_middleFive_quotient_action
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* PSL(2,F))
    (s : HexagonStructure.RootReflection Q split i)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (hj : Nat.card (simpleRoot Q split j) = 4)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) (horder : orderOf c = 3)
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥)
    (hPJ : Q.tits.standardParabolic {Q.simple i} ≤
      normalizer (middleFive Q split i j : Set (X ⧸ Q.D))) :
    ∃ hn : ((middleFive Q split i j).subgroupOf (simpleRemainder Q split i)).Normal,
      letI := hn
      ∃ φ : (rankOne Q split i ⊔ (Q.tits.B ⊓ Q.tits.N) : Subgroup (X ⧸ Q.D)) →*
          MulAut ((simpleRemainder Q split i) ⧸
            (middleFive Q split i j).subgroupOf (simpleRemainder Q split i)),
        (∀ (r : (rankOne Q split i ⊔ (Q.tits.B ⊓ Q.tits.N) : Subgroup (X ⧸ Q.D)))
          (v : simpleRemainder Q split i),
          ∃ w : simpleRemainder Q split i,
            (w : X ⧸ Q.D) = (r : X ⧸ Q.D)*(v : X ⧸ Q.D)*(r : X ⧸ Q.D)⁻¹ ∧
            φ r (QuotientGroup.mk v) = QuotientGroup.mk w) ∧
        ∀ D : Subgroup ((simpleRemainder Q split i) ⧸
            (middleFive Q split i j).subgroupOf (simpleRemainder Q split i)),
          (∀ r, ∀ x ∈ D, φ r x ∈ D) → D = ⊥ ∨ D = ⊤ := by
  let V := simpleRemainder Q split i
  let J := middleFive Q split i j
  let A := rankOne Q split i ⊔ (Q.tits.B ⊓ Q.tits.N)
  have hVP : V ≤ Q.tits.standardParabolic {Q.simple i} :=
    inf_le_left.trans (split.U_le.trans (Q.tits.B_le_standardParabolic _))
  have hAP : A ≤ Q.tits.standardParabolic {Q.simple i} :=
    sup_le (rankOne_le_parabolic Q split i)
      (inf_le_left.trans (Q.tits.B_le_standardParabolic _))
  have hAV : A ≤ normalizer (V : Set (X ⧸ Q.D)) :=
    hAP.trans (remainder_parabolic_normalizes Q split i hKi)
  let hn : (J.subgroupOf V).Normal := normal_subgroupOf_of_le_normalizer (hVP.trans hPJ)
  refine ⟨hn,?_⟩
  let := hn
  obtain ⟨φ,hφ,hirr⟩ := quotient_action_irreducible A V J
    (middleFive_le_remainder Q split hm i j hij) hAV (hAP.trans hPJ) (by
      intro C hJC hCV hAC
      exact separated_binary_middleFive_overgroup Q split hm i j hij hKi hKj μj s hi hj c
        horder hc C hJC hCV (le_sup_left.trans hAC) (le_sup_right.trans hAC))
  exact ⟨φ,fun r v => ⟨V.normalizerMonoidHom (inclusion hAV r) v,rfl,hφ r v⟩,hirr⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
