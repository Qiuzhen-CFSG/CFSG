module
public import Theory.GroupAction.FiveSmallDerived
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSuzukiLayers

/-!
# Excluding the pair of small Suzuki root actors

The actual reflection/root-involution product has order five and moves
both the radical and its Frattini subgroup. Coprime Frattini faithfulness
keeps its action nontrivial on the radical Frattini quotient. The exact
five-root product gives radical order 1024, so the two moving layers bound
the fixed subgroup by four. The previously proved bound |V′| ≤ 16 then
makes V′ central by the coprime-action lemma.

The opposite actual order-four root has nonzero cubic displacement on its
radical Frattini quotient. Class at most two forces that displacement to
vanish, giving the contradiction. Every action is induced by conjugation
in the same marked quotient, and neither root actor is assumed perfect.

Source: Fong--Seitz I (5H), printed p.30. The original/geometric application
in `FongSeitzBinary.HexagonStructure.SuzukiCatalogue` includes both the
Sz(2) and D₁₀ original quotient constructors.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups Pointwise IsMulCommutative commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource GTwoSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The literal small-pair radical has class at most two. -/
theorem smallSuzuki_pair_classTwo (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup 0)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup 0) :
    ⁅simpleRemainder Q split j,⁅simpleRemainder Q split j,simpleRemainder Q split j⁆⁆ = ⊥ := by
  let d := radicalSection Q split j hKj
  let f := frattiniSection Q split j d
  let V := d.numerator
  obtain ⟨s,u,hu,hc⟩ := smallSuzuki_exists_oddProduct Q split j μj νj
  let c : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩*u
  let A := zpowers c
  let : MulDistribMulAction A V :=
    MulDistribMulAction.compHom V (d.numeratorAction.comp A.subtype)
  let : IsInvariant A V (frattini V) := isInvariant_of_characteristic _
  let a : A := ⟨c,mem_zpowers c⟩
  have hA : Nat.card A = 5 := (Nat.card_zpowers c).trans hc
  have hB : rootAt Q split j (Q.simple i) ≤ V :=
    (le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hm i j hij)
  obtain ⟨x,hx⟩ := suzuki_conjugate_exists_nontrivial_square Q split j i νj
  have hx1 : x ≠ 1 := fun he => hx (by rw [he,one_pow])
  have hmove := ownRoot_oddProduct_moves_section Q split hm i j hij s u hu d rfl x hx1
    (hB x.property)
  have hfmove := ownRoot_oddProduct_moves_section Q split hm i j hij s u hu f rfl (x^2) hx
    (by
      let : Fact (IsPGroup 2 V) := ⟨d.isTwo⟩
      exact ⟨(inclusion hB x)^2,pth_power_mem_frattini_of_isPGroup (p := 2) _,rfl⟩)
  have hF : FixedPoints.subgroup A (frattini V) ≠ ⊤ := by
    intro he
    apply hfmove
    ext z
    induction z using QuotientGroup.induction_on with
    | H z =>
      rw [f.action_mk]
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      obtain ⟨v,hv,hvz⟩ := z.property
      have hvf : a • (⟨v,hv⟩ : frattini V) = ⟨v,hv⟩ :=
        (show (⟨v,hv⟩ : frattini V) ∈ FixedPoints.subgroup A (frattini V) from he ▸ mem_top _) a
      have hh := congrArg (fun t : frattini V => ((t : V) : X ⧸ Q.D)) hvf
      change (d.numeratorAction c v : X ⧸ Q.D) = v at hh
      rw [d.numeratorAction_apply] at hh
      rw [f.numeratorAction_apply]
      change (v : X ⧸ Q.D) = (z : X ⧸ Q.D) at hvz
      change (c : X ⧸ Q.D)*(z : X ⧸ Q.D)*(c : X ⧸ Q.D)⁻¹ = (z : X ⧸ Q.D)
      rwa [hvz] at hh
  have hQ : letI : MulDistribMulAction A (V ⧸ frattini V) :=
      quotientMulDistribMulAction (frattini V) inferInstance
      FixedPoints.subgroup A (V ⧸ frattini V) ≠ ⊤ := by
    let : MulDistribMulAction A (V ⧸ frattini V) :=
      quotientMulDistribMulAction (frattini V) inferInstance
    intro he
    apply hmove
    apply d.action_eq_one_of_odd c (by rw [hc]; decide)
    ext z
    induction z using QuotientGroup.induction_on with
    | H z =>
      have hz : a • (QuotientGroup.mk z : V ⧸ frattini V) = QuotientGroup.mk z :=
        (show (QuotientGroup.mk z : V ⧸ frattini V) ∈
          FixedPoints.subgroup A (V ⧸ frattini V) from he ▸ mem_top _) a
      change (QuotientGroup.mk (d.numeratorAction c z) : V ⧸ frattini V) = QuotientGroup.mk z at hz
      rw [d.effectiveAction_mk]
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hphi : frattini V ≤ d.effectiveDenominator := by
        rw [d.effectiveDenominator_eq]
        exact le_sup_left
      exact hphi (QuotientGroup.eq_iff_div_mem.mp hz)
  have hcI : Nat.card (simpleRoot Q split i) = 4 := by
    rw [Nat.card_congr νi.toEquiv,matrixRoot_card]; norm_num
  have hcJ : Nat.card (simpleRoot Q split j) = 4 := by
    rw [Nat.card_congr νj.toEquiv,matrixRoot_card]; norm_num
  have hcV : Nat.card V = 1024 := by
    have hall := unipotent_card_even Q split 3 hm
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    have hU : Nat.card split.U = 4096 := by
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact (hij rfl).elim
      · norm_num [hcI,hcJ] at hall ⊢; exact hall
      · norm_num [hcI,hcJ] at hall ⊢; exact hall
      · exact (hij rfl).elim
    have hv := unipotent_card_simple Q split j
    rw [hU,hcJ] at hv
    change Nat.card (simpleRemainder Q split j) = 1024
    omega
  have hfix := Theory.GroupAction.fixed_card_le_four_of_two_five_layers hA d.isTwo hcV
    (frattini V) hF hQ
  have hD : Nat.card (commutator V) ≤ 16 := by
    have hh := smallSuzuki_pair_derived_card_le_sixteen Q split hm i j hij hKi hKj μj νi νj
    rw [←map_subtype_commutator,card_map_of_injective (simpleRemainder Q split j).subtype_injective] at hh
    exact hh
  have hcentral := Theory.GroupAction.derived_central_of_small_five_fixed_subgroup hA d.isTwo hfix hD
  change ⁅V,⁅V,V⁆⁆ = ⊥
  rw [←map_subtype_commutator]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro v hv z hz
  obtain ⟨z,hz,rfl⟩ := hz
  exact congrArg Subtype.val ((mem_center_iff.mp (hcentral hz)) ⟨v,hv⟩).symm

/-- The class-two conclusion contradicts the actual cubic root displacement. -/
theorem smallSuzuki_pair_excluded (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup 0)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup 0)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup 0) : False :=
  smallSuzuki_opposite_radical_not_classTwo Q split hm j i hij.symm hKj hKi μi νi
    (smallSuzuki_pair_classTwo Q split hm i j hij hKi hKj μj νi νj)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
