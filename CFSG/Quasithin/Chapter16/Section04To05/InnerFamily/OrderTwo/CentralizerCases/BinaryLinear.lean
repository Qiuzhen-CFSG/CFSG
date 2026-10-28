module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.InnerExclusions
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.HigherLinear
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.BinaryLinear.EightModel
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.BinaryLinear.FiveModel

/-!
# The full eight-point action in the binary higher-linear cases

An actual marking L/Z(L) ≃ A₈ gives a faithful map H* → S₈, where
H* = N_G(L)/C_G(L). Its image contains A₈ and the given outer actor, so
already L*T* maps onto S₈. Faithfulness proves L*T* = H*: there are no
additional elements of H* left outside the permutation calculation.

The resulting equivalences preserve L*, the actor r*, and the embedded
image of O²(C_L(r)). In particular the entire C_H*(L*r) is identified with
the permutation centralizer of the actual fixed two-residual in A₈.
An outer involution has cycle type {2} or {2,2,2}; in the latter case the
marked `SymmetricEightCase` follows, including the specified r*.

The two permutation-centralizer computations prove the full alternative
for PSL₄(2), including the exceptional elementary abelian centralizer of
order four. For PSL₅(2), two explicit cubic matrices prove that the full
pointwise fixer of the graph residual has order at most two. The combined
assembly retains only the earlier outer-involution conjugacy theorem as
an explicit input; no centralizer bound or residual identification is assumed.
The quotient markings retain both binary dimensions and identify Z(L) with O₂(L) using
the component's trivial odd core, without discarding a covering kernel.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.2 and 16.1.4(8),(9), printed pp.1170–1172; the proof of 16.4.9(1),
printed p.1189. The false inner-j₂ row for PSL₅(2) is not used.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.BinaryLinear

open Theory.SpecificGroups.SymmetricEight.Involutions

variable {G : Type*} [Group G] (L : Subgroup G)

/-- The faithful eight-point action of the whole normalizer quotient. -/
noncomputable def eightAction (e : (L ⧸ center L) ≃* A) : ActionQuotient L →* S :=
  permutationAutEquiv.symm.toMonoidHom.comp (modelAction L e)

/-- Perfectness makes the action on the marked central quotient faithful. -/
theorem eightAction_injective [Group.IsPerfect L] (e : (L ⧸ center L) ≃* A) :
    Function.Injective (eightAction L e) :=
  permutationAutEquiv.symm.injective.comp (modelAction_injective L e)

/-- The action retains the actual embedded component element. -/
theorem eightAction_inner (e : (L ⧸ center L) ≃* A) (x : L) :
    eightAction L e (actionMap (le_normalizer (H := L)) x) = (modelProjection L e x).val := by
  change permutationAutEquiv.symm (MulAut.centralQuotientAction e
    (quotientAction L (quotientMap L ⟨x, le_normalizer x.property⟩))) = _
  rw [quotientAction_mk]
  have hc : L.normalizerMonoidHom ⟨x, le_normalizer x.property⟩ = MulAut.conj x := by
    ext y; rfl
  rw [hc]
  rw [MulAut.centralQuotientAction_conj]
  exact permutationAutEquiv.symm_apply_eq.mpr (permutationAutEquiv_inner _).symm

/-- The component image is exactly the specified alternating subgroup. -/
theorem eightAction_component (e : (L ⧸ center L) ≃* A) :
    (actionImage L L).map (eightAction L e) = alternatingGroup (Fin 8) := by
  ext q
  constructor
  · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩
    change eightAction L e (actionMap (le_normalizer (H := L)) (⟨x, hx⟩ : L)) ∈ _
    rw [eightAction_inner]
    exact (modelProjection L e ⟨x, hx⟩).property
  · intro hq
    obtain ⟨x, hx⟩ := e.surjective ⟨q, hq⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center L) x
    refine ⟨actionMap (le_normalizer (H := L)) y, mem_actionImage _ y.property, ?_⟩
    rw [eightAction_inner]
    exact congrArg Subtype.val hx

/-- The chosen outer element induces an odd permutation. -/
theorem eightAction_outer [IsQuasisimple L] (e : (L ⧸ center L) ≃* A)
    {r : G} (hn : r ∈ normalizer (L : Set G))
    (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    eightAction L e (actionElement L r hn) ∉ alternatingGroup (Fin 8) := by
  intro ha
  apply modelAction_outer L e r hn hout
  have hi := (permutationAutEquiv_mem_inner _).mpr ha
  change permutationAutEquiv (permutationAutEquiv.symm _) ∈ _ at hi
  rw [MulEquiv.apply_symm_apply] at hi
  obtain ⟨x, hx⟩ := hi
  exact ⟨x, hx.symm⟩

variable [Finite G] {T : Sylow 2 G} {z g : G} {R : Subgroup G}

/-- The component together with the Sylow subgroup already maps onto S₈. -/
theorem eightAction_join_top [IsQuasisimple L] (e : (L ⧸ center L) ≃* A)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    (actionImage L (L ⊔ (T : Subgroup G))).map (eightAction L e) = ⊤ := by
  apply top_unique
  rw [← alternating_sup_zpowers_eq_top (eightAction_outer L e
    (h.sylow_normalizes (h.le_sylow hr)) hout)]
  apply sup_le
  · rw [← eightAction_component L e]
    exact map_mono (actionImage_mono L le_sup_left)
  · apply zpowers_le.mpr
    apply mem_map_of_mem
    exact mem_actionImage _ ((le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G))
      (h.le_sylow hr))

/-- The full normalizer quotient has the whole symmetric group as its image. -/
theorem eightAction_surjective [IsQuasisimple L] (e : (L ⧸ center L) ≃* A)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) : Function.Surjective (eightAction L e) := by
  intro q
  have hq : q ∈ (actionImage L (L ⊔ (T : Subgroup G))).map (eightAction L e) := by
    rw [eightAction_join_top L e h hr hout]; trivial
  obtain ⟨a, _, ha⟩ := hq
  exact ⟨a, ha⟩

/-- Identify the full H*, not merely L*T*, with S₈. -/
noncomputable def eightEquiv [IsQuasisimple L] (e : (L ⧸ center L) ≃* A)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) : ActionQuotient L ≃* S :=
  MulEquiv.ofBijective (eightAction L e)
    ⟨eightAction_injective L e, eightAction_surjective L e h hr hout⟩

/-- There are no additional elements of H* outside L*T* in this row. -/
theorem eight_join_eq_top [IsQuasisimple L] (e : (L ⧸ center L) ≃* A)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    actionImage L (L ⊔ (T : Subgroup G)) = ⊤ := by
  apply top_unique
  intro a _
  have ha : eightAction L e a ∈
      (actionImage L (L ⊔ (T : Subgroup G))).map (eightAction L e) := by
    rw [eightAction_join_top L e h hr hout]; trivial
  obtain ⟨b, hb, hba⟩ := ha
  exact eightAction_injective L e hba ▸ hb

/-- The induced eight-point marking of the actual L*T*. -/
noncomputable def eightJoinEquiv [IsQuasisimple L] (e : (L ⧸ center L) ≃* A)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    actionImage L (L ⊔ (T : Subgroup G)) ≃* S :=
  (MulEquiv.subgroupCongr (eight_join_eq_top L e h hr hout)).trans
    (Subgroup.topEquiv.trans (eightEquiv L e h hr hout))

/-- The restricted marking agrees pointwise with the full normalizer action. -/
theorem eightJoinEquiv_apply [IsQuasisimple L] (e : (L ⧸ center L) ≃* A)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (a : actionImage L (L ⊔ (T : Subgroup G))) :
    eightJoinEquiv L e h hr hout a = eightAction L e a.val := rfl

/-- The marking of L*T* takes its actual subgroup L* onto A₈. -/
theorem eightJoinEquiv_component [IsQuasisimple L] (e : (L ⧸ center L) ≃* A)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    ((actionImage L L).subgroupOf (actionImage L (L ⊔ (T : Subgroup G)))).map
      (eightJoinEquiv L e h hr hout).toMonoidHom = alternatingGroup (Fin 8) := by
  rw [← eightAction_component L e]
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.val, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, actionImage_mono L le_sup_left ha⟩, ha, rfl⟩

/-- The three-transposition row supplies all markings in source case (II). -/
theorem eight_symmetricCase [IsQuasisimple L] (e : (L ⧸ center L) ≃* A)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hcycle : (eightAction L e
      (actionElement L r (h.sylow_normalizes (h.le_sylow hr)))).cycleType = {2, 2, 2}) :
    SymmetricEightCase T L r := by
  refine ⟨eightJoinEquiv L e h hr hout, eightJoinEquiv_component L e h hr hout,
    h.sylow_normalizes (h.le_sylow hr), ?_⟩
  exact ⟨⟨_, mem_actionImage _ ((le_sup_right : (T : Subgroup G) ≤
    L ⊔ (T : Subgroup G)) (h.le_sylow hr))⟩, rfl, hcycle⟩

omit [Finite G] in
/-- The permutation image of D* is the embedded image of the actual residual. -/
theorem eightAction_residual (e : (L ⧸ center L) ≃* A) (r : G) :
    (actionImage L (OuterResidual.involutionResidual L r)).map (eightAction L e) =
      (modelResidual L e r).map (alternatingGroup (Fin 8)).subtype := by
  ext q
  constructor
  · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩
    let y : L := ⟨x, (OuterResidual.involutionResidual_le L r hx).1⟩
    refine ⟨modelProjection L e y, ⟨y, hx, rfl⟩, ?_⟩
    exact (eightAction_inner L e y).symm
  · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨actionMap (le_normalizer (H := L)) x, mem_actionImage _ hx,
      eightAction_inner L e x⟩

private theorem map_centralizer_equiv {X Y : Type*} [Group X] [Group Y]
    (f : X ≃* Y) (D : Subgroup X) :
    (centralizer (D : Set X)).map f.toMonoidHom =
      centralizer (D.map f.toMonoidHom : Set Y) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    intro y hy
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using hx (f y) (mem_map_of_mem _ hy)

/-- Transport the entire residual centralizer in H* to its permutation model. -/
theorem eightEquiv_residualCentralizer [IsQuasisimple L] (e : (L ⧸ center L) ≃* A)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    (residualCentralizer L r).map (eightEquiv L e h hr hout).toMonoidHom =
      centralizer ((modelResidual L e r).map (alternatingGroup (Fin 8)).subtype : Set S) := by
  rw [residualCentralizer, map_centralizer_equiv]
  exact congrArg (fun D : Subgroup S => centralizer (D : Set S)) (eightAction_residual L e r)

/-- The full residual centralizer, as a group, with the actual residual marking. -/
noncomputable def eightResidualCentralizerEquiv [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* A) (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    residualCentralizer L r ≃*
      centralizer ((modelResidual L e r).map (alternatingGroup (Fin 8)).subtype : Set S) :=
  ((eightEquiv L e h hr hout).subgroupMap (residualCentralizer L r)).trans
    (MulEquiv.subgroupCongr (eightEquiv_residualCentralizer L e h hr hout))

/-- The two even cycle types are impossible for the specified outer involution. -/
theorem eight_outer_cycleType [IsQuasisimple L] (e : (L ⧸ center L) ≃* A)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    (eightAction L e (actionElement L r (h.sylow_normalizes (h.le_sylow hr)))).cycleType = {2} ∨
      (eightAction L e (actionElement L r (h.sylow_normalizes (h.le_sylow hr)))).cycleType =
        {2, 2, 2} := by
  let q := eightAction L e (actionElement L r (h.sylow_normalizes (h.le_sylow hr)))
  have hq : orderOf q = 2 :=
    (orderOf_injective (eightAction L e) (eightAction_injective L e) _).trans
      ((actionElement_order L h hr).trans hr2)
  have hodd := eightAction_outer L e (h.sylow_normalizes (h.le_sylow hr)) hout
  rcases involution_cycleType hq with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · exfalso
    apply hodd
    apply Equiv.Perm.mem_alternatingGroup.mpr
    change Equiv.Perm.sign q = 1
    rw [Equiv.Perm.sign_of_cycleType, h2]
    decide
  · exact Or.inr h3
  · exfalso
    apply hodd
    apply Equiv.Perm.mem_alternatingGroup.mpr
    change Equiv.Perm.sign q = 1
    rw [Equiv.Perm.sign_of_cycleType, h4]
    decide

/-- The marked residual is the fixed two-residual of the same permutation actor. -/
theorem eight_modelResidual_eq [IsQuasisimple L] (e : (L ⧸ center L) ≃* A)
    (hodd : pPrimeCore 2 L = ⊥) (r : G) (hn : r ∈ normalizer (L : Set G)) :
    modelResidual L e r = LiePreliminaries.fixedTwoResidual A
      (permutationAutEquiv (eightAction L e (actionElement L r hn))) := by
  rw [modelResidual_eq_fixedTwoResidual L e r hn hodd]
  congr 1
  exact (permutationAutEquiv.apply_symm_apply _).symm

/-- Identify the full centralizer with the intrinsic permutation calculation.
The trivial odd core is available from `component_oddCore`; the equivalence
retains central covers through the fixed-residual projection theorem. -/
noncomputable def eightFixedResidualCentralizerEquiv [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* A) (hodd : pPrimeCore 2 L = ⊥)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    residualCentralizer L r ≃*
      centralizer ((LiePreliminaries.fixedTwoResidual A
        (permutationAutEquiv (eightAction L e
          (actionElement L r (h.sylow_normalizes (h.le_sylow hr)))))).map
            (alternatingGroup (Fin 8)).subtype : Set S) :=
  (eightResidualCentralizerEquiv L e h hr hout).trans
    (MulEquiv.subgroupCongr (congrArg
      (fun D : Subgroup A => centralizer (D.map (alternatingGroup (Fin 8)).subtype : Set S))
      (eight_modelResidual_eq L e hodd r _)))

/-- The actual A₈ marking starting from the source PSL₄(2) quotient convention. -/
noncomputable def fourQuotientEquiv [IsQuasisimple L] (hodd : pPrimeCore 2 L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 4 2) :
    (L ⧸ center L) ≃* A :=
  (LiePreliminaries.centerQuotientEquivTwoCore hodd).trans
    (LiePreliminaries.higherLinearFourAlternatingEquiv hmodel)

/-- The actual natural binary model, retaining PSL₅(2) as well as PSL₄(2). -/
noncomputable def binaryQuotientEquiv [IsQuasisimple L] (hodd : pPrimeCore 2 L = ⊥)
    {n : ℕ} (hn : 0 < n) (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) n 2) :
    (L ⧸ center L) ≃* _root_.BinaryLinear.OuterCyclic.LinearGroup n :=
  (LiePreliminaries.centerQuotientEquivTwoCore hodd).trans
    (LiePreliminaries.higherLinearEquiv hn hmodel)

omit [Finite G] in
private theorem modelAction_trans {X Y : Type*} [Group X] [Group Y]
    (e : (L ⧸ center L) ≃* X) (f : X ≃* Y) (a : ActionQuotient L) :
    modelAction L (e.trans f) a = MulAut.congr f (modelAction L e a) := by
  ext x
  rfl

open _root_.BinaryLinear.OuterCyclic

/-- Change the actual quotient marking by the conjugating element in the
PSL₅(2) outer-involution theorem. The actor and its embedded fixed two-residual
then agree with the canonical inverse-transpose model. The conjugacy is an
earlier-source input; no residual or pointwise-fixer bound is assumed. -/
theorem five_graph_marking [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) (e : (L ⧸ center L) ≃* LinearGroup 5)
    (r : G) (hn : r ∈ normalizer (L : Set G))
    (hconj : ∃ x : LinearGroup 5, MulAut.congr (MulAut.conj x)
      (modelAction L e (actionElement L r hn)) = graphLinear 5) :
    ∃ f : (L ⧸ center L) ≃* LinearGroup 5,
      modelAction L f (actionElement L r hn) = graphLinear 5 ∧
      modelResidual L f r = LiePreliminaries.fixedTwoResidual (LinearGroup 5) (graphLinear 5) := by
  obtain ⟨x, hx⟩ := hconj
  let f := e.trans (MulAut.conj x)
  have ha : modelAction L f (actionElement L r hn) = graphLinear 5 := by
    rw [modelAction_trans]
    exact hx
  refine ⟨f, ha, ?_⟩
  rw [modelResidual_eq_fixedTwoResidual L f r hn hodd, ha]

omit [Finite G] in
/-- Changing the A₈ marking conjugates the same eight-point actor. -/
theorem eightAction_change (e : (L ⧸ center L) ≃* A) (s : S) (a : ActionQuotient L) :
    eightAction L (e.trans (permutationAutEquiv s)) a = s * eightAction L e a * s⁻¹ := by
  apply permutationAutEquiv.injective
  have ha (f : (L ⧸ center L) ≃* A) :
      permutationAutEquiv (eightAction L f a) = modelAction L f a :=
    permutationAutEquiv.apply_symm_apply _
  rw [ha, map_mul, map_mul, map_inv, ha]
  ext x
  rfl

omit [Finite G] in
/-- Equal cycle types give a compatible marking of the specified actor. -/
theorem eight_marking (e : (L ⧸ center L) ≃* A) (a : ActionQuotient L) (q : S)
    (hq : (eightAction L e a).cycleType = q.cycleType) :
    ∃ f : (L ⧸ center L) ≃* A, eightAction L f a = q := by
  obtain ⟨s, hs⟩ := isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr hq)
  exact ⟨e.trans (permutationAutEquiv s), (eightAction_change L e s a).trans hs⟩

section EightCases
variable [IsQuasisimple L]

/-- The transposition row has full residual centralizer of order two. -/
theorem eight_onePair_card (e : (L ⧸ center L) ≃* A) (hodd : pPrimeCore 2 L = ⊥)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hq : (eightAction L e (actionElement L r
      (h.sylow_normalizes (h.le_sylow hr)))).cycleType = {2}) :
    Nat.card (residualCentralizer L r) = 2 := by
  obtain ⟨f, hf⟩ := eight_marking L e (actionElement L r _) onePair
    (hq.trans onePair_cycleType.symm)
  have hc := Nat.card_congr (eightFixedResidualCentralizerEquiv L f hodd h hr hout).toEquiv
  rw [hf] at hc
  exact hc.trans EightModel.onePair_card

/-- The exceptional row has the full E₄ centralizer and the required S₈ marking. -/
theorem eight_threePairs_data (e : (L ⧸ center L) ≃* A) (hodd : pPrimeCore 2 L = ⊥)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hq : (eightAction L e (actionElement L r
      (h.sylow_normalizes (h.le_sylow hr)))).cycleType = {2, 2, 2}) :
    Nat.card (residualCentralizer L r) = 4 ∧
      IsElementaryAbelian 2 (residualCentralizer L r) ∧ SymmetricEightCase T L r := by
  obtain ⟨f, hf⟩ := eight_marking L e (actionElement L r _) threePairs
    (hq.trans threePairs_cycleType.symm)
  let c : residualCentralizer L r ≃* EightModel.fullCentralizer threePairs :=
    (eightFixedResidualCentralizerEquiv L f hodd h hr hout).trans
      (MulEquiv.subgroupCongr (by rw [hf]; rfl))
  refine ⟨(Nat.card_congr c.toEquiv).trans EightModel.threePairs_card, ?_,
    eight_symmetricCase L e h hr hout hq⟩
  let := EightModel.threePairs_elementary
  refine {
    toIsMulCommutative := ⟨⟨fun x y => c.injective (by
      rw [map_mul, map_mul]; exact mul_comm _ _)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => ?_) }
  apply c.injective
  rw [map_pow, map_one]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 _) _

/-- Exhaust the outer-involution alternatives for an actual A₈ quotient marking. -/
theorem eight_alternative (e : (L ⧸ center L) ≃* A) (hodd : pPrimeCore 2 L = ⊥)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) : ResidualCentralizerAlternative T L r := by
  rcases eight_outer_cycleType L e h hr hr2 hout with hq | hq
  · left
    apply sylow_card_two_of_not_four_dvd L h hr hr2
    rw [eight_onePair_card L e hodd h hr hout hq]
    decide
  · obtain ⟨hc, he, hs⟩ := eight_threePairs_data L e hodd h hr hout hq
    exact Or.inr ⟨hc, he, Or.inl hs⟩

omit [IsQuasisimple L] in
/-- The full PSL₄(2) branch, using only the given intersection setup and (E1). -/
theorem four_alternative (hG : HasEvenTypeCentralizers G)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 4 2) :
    ResidualCentralizerAlternative T L r := by
  let := h.component.quasisimple
  have hodd := component_oddCore hG h.toCentralComponentSetup
  exact eight_alternative L (fourQuotientEquiv L hodd hmodel) hodd h hr hr2 hout
end EightCases

/-- The actual PSL₅(2) centralizer bound after the earlier source conjugacy step. -/
theorem five_alternative_of_marked_conjugacy [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) (e : (L ⧸ center L) ≃* LinearGroup 5)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hconj : ∃ x : LinearGroup 5, MulAut.congr (MulAut.conj x)
      (modelAction L e (actionElement L r (h.sylow_normalizes (h.le_sylow hr)))) =
        graphLinear 5) : ResidualCentralizerAlternative T L r := by
  let : Finite (LinearGroup 5) := Finite.of_equiv (L ⧸ center L) e.toEquiv
  obtain ⟨f, _, hf⟩ := five_graph_marking L hodd e r _ hconj
  apply alternative_of_fixer_not_four_dvd L f h hr hr2
  rw [hf]
  exact FiveModel.fixer_not_four_dvd

/-- Assemble both binary dimensions with only the earlier outer-involution
conjugacy theorem explicit. The arbitrary group class specializes to
`KnownSimple.IsKnownSimple`. Both model centralizer calculations are discharged;
this does not claim that the remaining conjugacy premise has been proved. -/
theorem binary_alternative_of_graph_conjugacy {K : GroupClass}
    (hG : Hypothesis1611 K G)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) (_hLie : IsEvenTypeLieComponent L)
    (hmodel : ∃ n, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) n 2)
    (hgraph : ∀ a : MulAut (LinearGroup 5), orderOf a = 2 →
      a ∉ MulAut.innerSubgroup (LinearGroup 5) →
      ∃ x : LinearGroup 5, MulAut.congr (MulAut.conj x) a = graphLinear 5) :
    ResidualCentralizerAlternative T L r := by
  obtain ⟨n, hn, hm⟩ := hmodel
  rcases hn with rfl | rfl
  · exact four_alternative L hG.evenType h hr hr2 hout hm
  · let := h.component.quasisimple
    have hodd := component_oddCore hG.evenType h.toCentralComponentSetup
    let e := binaryQuotientEquiv L hodd (by decide : 0 < 5) hm
    apply five_alternative_of_marked_conjugacy L hodd e h hr hr2
    apply hgraph
    · exact (modelAction_order L e h hr).trans hr2
    · rintro ⟨x, hx⟩
      exact modelAction_outer L e r _ hout ⟨x, hx.symm⟩


end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.BinaryLinear
