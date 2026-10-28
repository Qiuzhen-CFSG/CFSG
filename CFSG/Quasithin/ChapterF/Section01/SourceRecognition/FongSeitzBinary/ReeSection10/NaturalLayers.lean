module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.PhiFaithfulness
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LayerOrders
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PerpendicularObstruction
public import Theory.Representation.Suzuki.MinimalDegree
public import Theory.Representation.Suzuki.SmallDegree
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.BinaryNatural

/-!
# Faithful natural coordinates on both Section 10 Suzuki layers

The reflection moves a nontrivial linear-root vector modulo T2. The
rank-one kernel criterion then gives faithfulness, also for Sz(2). Both
layers have order q^4, so the faithful minimal-degree theorem gives
irreducibility. The nonbinary small-degree theorem and the separate
five-coset argument at q = 2 identify the actual actions with the natural
matrix action on the same field of order 2^(2m+1).

The resulting binary-linear coordinates intertwine literal source
conjugation. Their alignment with the distinguished root lines and the
field parameters of (10.7)--(10.9) remains a separate step.
Source: Fong--Seitz II (1974), printed pp.221--224, (10.4) and (10.11).
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

include c in
private theorem middle_le_linearRemainder :
    ∀ A ∈ middleFactors Q split, A ≤ simpleRemainder Q split 0 := by
  have hs (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using
      (Q.tits.involutions _ (Q.simple_mem k)).2)
  have hss (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
  have hm := c.rotation_eight
  have hl (b : Bool) := And.intro
    (wordLength_alternatingWord Q b (n := 1) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 2) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 3) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 4) (by omega))
    (wordLength_alternatingWord Q b (n := 5) (by omega)))))
  have hf := hl false
  have ht := hl true
  simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,
    Bool.not_true,mul_one] at hf ht
  intro A hA
  simp only [middleFactors,List.mem_cons,List.not_mem_nil,or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl
  all_goals
    apply rootAt_le_remainder
    all_goals
      simp [positiveKind,positiveWord,mul_inv_rev,hs,mul_assoc,
        ←mul_assoc (Q.simple 0) (Q.simple 0),
        hss,one_mul,Q.tits.wordLength_one,
        hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2,
        ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1]

include c in
theorem T2_le_linearRemainder : T2 Q split ≤ simpleRemainder Q split 0 := by
  apply sup_le
  · intro x hx
    have hx' : x ∈ (phi (simpleRemainder Q split 1) : Set _) := hx
    rw [←phiProduct_range Q split c] at hx'
    obtain ⟨p,rfl⟩ := hx'
    exact rootProduct_mem (middleFactors Q split) _ (middle_le_linearRemainder Q split c)
      (phiTupleInclusion Q split p)
  · exact middle_le_linearRemainder Q split c _ (by simp [middleFactors,perpendicularSuzuki,
      positiveRoot,positiveKind,positiveWord])

include c in
theorem V2_mover_moves : (V2Section Q split c).action
    (frattiniMover Q split 1 m c.suzuki c.suzukiBorel) ≠ 1 := by
  have hK0 : simpleRemainder Q split 0 ≤ localKernel Q 0 :=
    remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow c.linearBorel
      (linear_normalizer_index c.linearSylow)
  let A := rootAt Q split 0 (Q.simple 1)
  let B := simpleRoot Q split 0
  let s := involutoryRootReflection Q split 1 (UnitarySource.actorReflection Q split 1)
  let u : rankOne Q split 1 := inclusion le_sup_left (suzukiParameter Q split 1 m c.suzuki c.suzukiBorel 0 1)
  let d := V2Section Q split c
  obtain ⟨a,ha⟩ : ∃ a : A, a ≠ 1 :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (rootAt_ne_bot Q split 0 _)
  have hAV1 : A ≤ simpleRemainder Q split 1 :=
    (octagon_three_roots_le_remainder Q split c.rotation_eight 1 0 (by decide)).1
  have hAV0 : A ≤ simpleRemainder Q split 0 := by
    have hs : (Q.simple 1)⁻¹ = Q.simple 1 := inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem 1)).2)
    have hl (b : Bool) (k : ℕ) (hk : k ≤ 8) := wordLength_alternatingWord Q b
      (n := k) (by simpa only [c.rotation_eight] using hk)
    have h1 := hl true 1 (by decide)
    have h2 := hl true 2 (by decide)
    have h2' := hl false 2 (by decide)
    have h3 := hl false 3 (by decide)
    simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,
      Bool.not_true,mul_one] at h1 h2 h2' h3
    apply rootAt_le_remainder Q split 0 0 (Q.simple 1)
    · simpa only [hs] using h2.trans (congrArg (·+1) h1).symm
    · simpa only [hs,mul_assoc] using h3.trans (congrArg (·+1) h2').symm
  let v : d.numerator := ⟨a,hAV1 a.property⟩
  have hcomm : ⁅simpleRoot Q split 1,A⁆ = ⊥ :=
    adjacent_commutator_eq_bot Q split c.rotation_eight 1 0 (by decide)
      (remainder_le_kernel Q split c) hK0
  have huc : Commute (u : X ⧸ Q.D) (a : X ⧸ Q.D) :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm
      (suzukiParameter Q split 1 m c.suzuki c.suzukiBorel 0 1).property) _ a.property).symm
  have hsq : (s.val : X ⧸ Q.D)*(s.val : X ⧸ Q.D) = 1 := by
    simpa only [pow_two] using involutoryRootReflection_sq Q split 1 (UnitarySource.actorReflection Q split 1)
  have hinv : (s.val : X ⧸ Q.D)⁻¹ = (s.val : X ⧸ Q.D) := inv_eq_of_mul_eq_one_right hsq
  have hAB : rightConjugate A (s.val : X ⧸ Q.D) = B := by
    rw [rootAt_right Q split 0 _ _ s.val s.class_eq]
    have ht : Q.simple 1*Q.simple 1 = 1 := by
      simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem 1)).2
    rw [ht,rootAt_one]
  let y : B := ⟨(s.val : X ⧸ Q.D)*a*(s.val : X ⧸ Q.D)⁻¹,by
    rw [←hAB]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)*a*(s.val : X ⧸ Q.D)⁻¹)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ A
    simpa only [hinv,mul_assoc,←mul_assoc (s.val : X ⧸ Q.D) (s.val : X ⧸ Q.D),
      hsq,one_mul,mul_one] using a.property⟩
  have hv : (d.numeratorAction (frattiniMover Q split 1 m c.suzuki c.suzukiBorel) v : X ⧸ Q.D) = y := by
    change ((s.val : X ⧸ Q.D)*(u : X ⧸ Q.D))*a*
      ((s.val : X ⧸ Q.D)*(u : X ⧸ Q.D))⁻¹ = (s.val : X ⧸ Q.D)*a*(s.val : X ⧸ Q.D)⁻¹
    calc
      _ = (s.val : X ⧸ Q.D)*((u : X ⧸ Q.D)*a*(u : X ⧸ Q.D)⁻¹)*
          (s.val : X ⧸ Q.D)⁻¹ := by simp only [mul_inv_rev,mul_assoc]
      _ = _ := by rw [huc.eq,mul_inv_cancel_right]
  intro he
  have hz : d.numeratorAction (frattiniMover Q split 1 m c.suzuki c.suzukiBorel) v / v ∈ d.denominator := by
    apply QuotientGroup.eq_iff_div_mem.mp
    exact (d.action_mk _ v).symm.trans (congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk v)) he)
  have hz' : (y : X ⧸ Q.D)/(a : X ⧸ Q.D) ∈ T2 Q split := by
    change (d.numeratorAction _ v : X ⧸ Q.D)/(v : X ⧸ Q.D) ∈ T2 Q split at hz
    simpa only [hv] using hz
  have hy : (y : X ⧸ Q.D) ∈ simpleRemainder Q split 0 := by
    simpa only [div_mul_cancel] using (simpleRemainder Q split 0).mul_mem
      (T2_le_linearRemainder Q split c hz') (hAV0 a.property)
  have hy1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split 0) y.property hy
  have ha1 : (a : X ⧸ Q.D) = 1 := (MulAut.conj (s.val : X ⧸ Q.D)).injective
    (hy1.trans (map_one _).symm)
  exact ha (Subtype.ext ha1)

include c in
theorem V2_action_injective : Function.Injective (V2Section Q split c).action :=
  sectionAction_injective_of_mover Q split c _ (V2_mover_moves Q split c)

include c in
theorem V2Representation_injective : Function.Injective (V2Representation Q split c) := by
  intro r s he
  apply V2_action_injective Q split c
  ext v
  exact Additive.ofMul.injective (congrArg
    (fun f : Module.End (ZMod 2) (Additive (V2Section Q split c).Carrier) => f (Additive.ofMul v)) he)

include c in
theorem suzukiV2Representation_injective : Function.Injective (suzukiV2Representation Q split c) :=
  (V2Representation_injective Q split c).comp
    (suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel).symm.injective

include c in
theorem V2_irreducible : (suzukiV2Representation Q split c).IsIrreducible :=
  (Representation.Suzuki.irreducible_of_faithful_small_card (suzukiV2Representation Q split c)
    (suzukiV2Representation_injective Q split c)
    (le_of_eq ((Nat.card_congr Additive.toMul).trans (V2_card Q split c)))).1

include c in
theorem phiCenter_irreducible : (suzukiPhiCenterRepresentation Q split c).IsIrreducible :=
  (Representation.Suzuki.irreducible_of_faithful_small_card (suzukiPhiCenterRepresentation Q split c)
    (suzukiPhiCenterRepresentation_injective Q split c)
    (le_of_eq ((Nat.card_congr Additive.toMul).trans (phiCenter_card Q split c)))).1

include c in
theorem V2_natural_of_pos (hm : 1 ≤ m) :
    Nonempty ((suzukiV2Representation Q split c).Equiv (Representation.SuzukiNatural.natural m)) :=
  Representation.SuzukiSmallDegree.natural_equiv_of_smallDegree hm _
    (suzukiV2Representation_injective Q split c) (V2_irreducible Q split c)
    (by rw [V2_finrank Q split c]; omega)

include c in
theorem phiCenter_natural_of_pos (hm : 1 ≤ m) :
    Nonempty ((suzukiPhiCenterRepresentation Q split c).Equiv (Representation.SuzukiNatural.natural m)) :=
  Representation.SuzukiSmallDegree.natural_equiv_of_smallDegree hm _
    (suzukiPhiCenterRepresentation_injective Q split c) (phiCenter_irreducible Q split c)
    (by rw [phiCenter_finrank Q split c]; omega)

/-- The first natural-module identification includes the full binary endpoint. -/
theorem V2_natural :
    Nonempty ((suzukiV2Representation Q split c).Equiv (Representation.SuzukiNatural.natural m)) := by
  by_cases hm : m = 0
  · subst m
    exact binary_natural_equiv _ (suzukiV2Representation_injective Q split c)
      (by simpa using V2_finrank Q split c)
  · exact V2_natural_of_pos Q split c (by omega)

/-- The Frattini/center layer has the same natural model, including m = 0. -/
theorem phiCenter_natural :
    Nonempty ((suzukiPhiCenterRepresentation Q split c).Equiv (Representation.SuzukiNatural.natural m)) := by
  by_cases hm : m = 0
  · subst m
    exact binary_natural_equiv _ (suzukiPhiCenterRepresentation_injective Q split c)
      (by simpa using phiCenter_finrank Q split c)
  · exact phiCenter_natural_of_pos Q split c (by omega)

/-- A chosen intertwiner on the actual V2 quotient. -/
def V2Coordinates : (suzukiV2Representation Q split c).Equiv
    (Representation.SuzukiNatural.natural m) := (V2_natural Q split c).some

/-- A chosen intertwiner on the actual Frattini/center quotient. -/
def phiCenterCoordinates : (suzukiPhiCenterRepresentation Q split c).Equiv
    (Representation.SuzukiNatural.natural m) := (phiCenter_natural Q split c).some

theorem V2Coordinates_source (r : rankOne Q split 1) (v : simpleRemainder Q split 1) :
    V2Coordinates Q split c
      (Additive.ofMul (QuotientGroup.mk ((V2Section Q split c).numeratorAction r v))) =
    Representation.SuzukiNatural.natural m (suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel r)
      (V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v))) := by
  rw [← suzukiV2Representation_source Q split c r v]
  exact (V2Coordinates Q split c).toIntertwiningMap.isIntertwining _ _ _ _

theorem phiCenterCoordinates_source (r : rankOne Q split 1)
    (v : (phiCenterSection Q split c).numerator) :
    phiCenterCoordinates Q split c
      (Additive.ofMul (QuotientGroup.mk ((phiCenterSection Q split c).numeratorAction r v))) =
    Representation.SuzukiNatural.natural m (suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel r)
      (phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk v))) := by
  rw [← suzukiPhiCenterRepresentation_source Q split c r v]
  exact (phiCenterCoordinates Q split c).toIntertwiningMap.isIntertwining _ _ _ _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
