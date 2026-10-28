module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiRankOne
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.RadicalDegree
public import Theory.SpecificGroups.Suzuki.RootCenter
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiRootLayers
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanActions
public import Mathlib.GroupTheory.Nilpotent

/-!
# The effective derived radical in the source octagon

For a positive Suzuki parameter, a conjugate of the simple Suzuki root
has nonzero derived subgroup. It lies in V = U ∩ U^s; the actual rank-one
reflection sends it to a disjoint root. Hence the action on [V,V] is
nontrivial. The prescribed natural panel marking now identifies the whole
actor with the concrete simple Suzuki group. Its conjugation action is
faithful, and the two-group kernel of the Frattini action is trivial.

Thus the literal derived Frattini section has binary dimension at least
4(2m+1). Combining its q^4 lower bound with the previously proved bound
on V/Φ(V) gives |Φ([V,V])| q^2 ≤ |U_j|^4. The two fields are independent.
All quotients use normality inside their actual numerator, and all actions
are the original conjugation action on the same marked quotient.

Source: Fong--Seitz I (1973), proof of (6H), printed p.52, the effective
modules preceding (6.1). The nonabelian-root argument requires m>0: the
Sz(2) root is cyclic, so its derived subgroup cannot supply this witness.
The binary derived-module argument, the centralizer bounds (6.1), and the
nonzero mixed commutator remain separate steps of the retained source proof.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)

def derivedRadicalSection : RootSection Q split i where
  numerator := ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆
  le_radical := commutator_le_self _
  normalized := by
    intro r hr
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (remainder_parabolic_normalizes Q split i hV
        (rankOne_le_parabolic Q split i hr))]
  denominator := ⊥
  invariant _ := map_bot _

private theorem octagon_lengths (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j) :
    Q.tits.wordLength (Q.simple i) = 1 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j) = 2 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i) = 3 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j) = 4 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i) = 5 := by
  have hh (b : Bool) := And.intro
    (wordLength_alternatingWord Q b (n := 1) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 2) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 3) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 4) (by omega))
    (wordLength_alternatingWord Q b (n := 5) (by omega)))))
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using hh false
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using hh true
  · exact (hij rfl).elim

private theorem rootAt_derived_nonzero (m : ℕ)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (hm : 0 < m) (w : Weyl Q) :
    ⁅rootAt Q split i w,rootAt Q split i w⁆ ≠ ⊥ := by
  intro hz
  let A := rootAt Q split i w
  let : IsMulCommutative A := commutator_self_eq_bot_iff.mp hz
  let e : A ≃* SuzukiRootSubgroup m :=
    (RootAction.conjugateEquiv (simpleRoot Q split i) (representative w)).trans
      (suzukiRootEquiv Q split i m μ hB)
  let : IsMulCommutative (SuzukiRootSubgroup m) := isMulCommutative_iff.mpr fun x y =>
    e.symm.injective (by rw [map_mul,map_mul,mul_comm])
  have hc := suzukiRootSubgroup_center_card m hm
  rw [center_eq_top, card_top, matrixRoot_card] at hc
  have hq : 1 < 2^(2*m+1) := Nat.one_lt_pow (by omega) (by decide)
  nlinarith

variable (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include hB in
theorem derivedRadical_numeratorAction_nontrivial (hm : rotationOrder Q = 8) (hmpos : 0 < m) :
    (derivedRadicalSection Q split i hV).numeratorAction ≠ 1 := by
  intro hz
  let j : Fin 2 := 1-i
  have hij : i ≠ j := by dsimp [j]; omega
  have hi := octagon_lengths Q i hm j hij
  have hj := octagon_lengths Q j hm i hij.symm
  have hs (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2)
  let A := rootAt Q split i (Q.simple j)
  have hAV : A ≤ simpleRemainder Q split i := by
    apply rootAt_le_remainder Q split i i (Q.simple j)
    · rw [hs,hj.2.1,hj.1]
    · rw [hs,hi.2.2.1,hi.2.1]
  have hAB : Disjoint A (rootAt Q split i (Q.simple j*Q.simple i)) := by
    apply rootAt_disjoint Q split i (Q.simple j) (Q.simple j*Q.simple i)
    simp only [mul_inv_rev,hs]
    simp only [← mul_assoc]
    rw [hi.2.2.2.2,hi.2.2.2.1]
  apply rootAt_derived_nonzero Q split i m μ hB hmpos (Q.simple j)
  apply eq_bot_iff.mpr
  intro a ha
  let d := derivedRadicalSection Q split i hV
  let s := UnitarySource.actorReflection Q split i
  let r : rankOne Q split i := ⟨s.val,s.mem_rankOne⟩
  let v : d.numerator := ⟨a,commutator_mono hAV hAV ha⟩
  have he := congrArg (fun f : rankOne Q split i →* MulAut d.numerator =>
    (f r⁻¹ v : X ⧸ Q.D)) hz
  change (s.val : X ⧸ Q.D)⁻¹*a*((s.val : X ⧸ Q.D)⁻¹)⁻¹ = a at he
  rw [inv_inv] at he
  have hc : a ∈ rootAt Q split i (Q.simple j*Q.simple i) := by
    rw [← rootAt_right Q split i (Q.simple j) (Q.simple i) s.val s.class_eq, ←he]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*(s.val : X ⧸ Q.D)⁻¹ ∈ A
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using
      (commutator_le_self A ha)
  exact disjoint_def.mp hAB (commutator_le_self A ha) hc

include hB in
theorem derivedRadical_numeratorAction_injective (hm : rotationOrder Q = 8) (hmpos : 0 < m) :
    Function.Injective (derivedRadicalSection Q split i hV).numeratorAction := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hmpos).1
  let : IsSimpleGroup (rankOne Q split i) :=
    (suzukiActorEquiv Q split i m μ hB).isSimpleGroup
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : (derivedRadicalSection Q split i hV).numeratorAction.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (derivedRadical_numeratorAction_nontrivial Q split i hV m μ hB hm hmpos
      (MonoidHom.ker_eq_top_iff.mp ht)).elim

include hB in
/-- The literal derived radical has a faithful effective action, for positive Suzuki parameters. -/
theorem derivedRadical_effectiveAction_injective (hm : rotationOrder Q = 8) (hmpos : 0 < m) :
    Function.Injective (derivedRadicalSection Q split i hV).effectiveAction := by
  let d := derivedRadicalSection Q split i hV
  let e := suzukiActorEquiv Q split i m μ hB
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hmpos).1
  let : IsSimpleGroup (rankOne Q split i) := e.isSimpleGroup
  let a := (quotientAut (frattini d.numerator)).comp d.numeratorAction
  have htwo : IsPGroup 2 a.ker :=
    (isPGroup_quotientAut_frattini_kernel d.isTwo).comap_of_injective d.numeratorAction
      (derivedRadical_numeratorAction_injective Q split i hV m μ hB hm hmpos)
  have ha : a.ker = ⊥ := by
    rcases (inferInstance : a.ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hR : IsPGroup 2 (rankOne Q split i) := by
        intro r
        obtain ⟨n,hn⟩ := htwo (⟨r,ht.symm ▸ mem_top r⟩ : a.ker)
        exact ⟨n,congrArg Subtype.val hn⟩
      let : Group.IsNilpotent (rankOne Q split i) := hR.isNilpotent
      exact (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hmpos
        (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)).elim
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro r hr
  have hd : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  have hr' : r ∈ a.ker := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini d.numerator) z
    change quotientAut (frattini d.numerator) (d.numeratorAction r)
      (QuotientGroup.mk' (frattini d.numerator) x) = _
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hx : d.numeratorAction r x / x ∈ d.effectiveDenominator := by
      apply QuotientGroup.eq_iff_div_mem.mp
      exact (d.effectiveAction_mk r x).symm.trans
        (congrArg (fun f : MulAut d.EffectiveCarrier => f (QuotientGroup.mk x)) hr)
    rwa [hd] at hx
  exact ha ▸ hr'

include hB in
theorem derivedRadical_effectiveRepresentation_injective
    (hm : rotationOrder Q = 8) (hmpos : 0 < m) :
    Function.Injective (derivedRadicalSection Q split i hV).effectiveRepresentation :=
  (derivedRadicalSection Q split i hV).effectiveRepresentation_injective
    (derivedRadical_effectiveAction_injective Q split i hV m μ hB hm hmpos)

include hB in
theorem derivedRadical_isEffective (hm : rotationOrder Q = 8) (hmpos : 0 < m) :
    (derivedRadicalSection Q split i hV).IsEffective := by
  unfold RootSection.IsEffective
  rw [(MonoidHom.ker_eq_bot_iff _).mpr
    (derivedRadical_effectiveAction_injective Q split i hV m μ hB hm hmpos)]
  exact bot_le

/-- The Suzuki module is the transported conjugation action on this exact source section. -/
def suzukiDerivedRepresentation : Representation (ZMod 2) (SuzukiMatrixGroup m)
    (Additive (derivedRadicalSection Q split i hV).EffectiveCarrier) :=
  (derivedRadicalSection Q split i hV).effectiveRepresentation.comp
    (suzukiActorEquiv Q split i m μ hB).symm.toMonoidHom

@[simp] theorem suzukiDerivedRepresentation_source
    (r : rankOne Q split i) (x : (derivedRadicalSection Q split i hV).numerator) :
    suzukiDerivedRepresentation Q split i hV m μ hB (suzukiActorEquiv Q split i m μ hB r)
      (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk
        ((derivedRadicalSection Q split i hV).numeratorAction r x)) := by
  change (derivedRadicalSection Q split i hV).effectiveRepresentation
    ((suzukiActorEquiv Q split i m μ hB).symm (suzukiActorEquiv Q split i m μ hB r)) _ = _
  rw [MulEquiv.symm_apply_apply,RootSection.effectiveRepresentation_mk]

include hB in
theorem suzukiDerivedRepresentation_injective (hm : rotationOrder Q = 8) (hmpos : 0 < m) :
    Function.Injective (suzukiDerivedRepresentation Q split i hV m μ hB) :=
  (derivedRadical_effectiveRepresentation_injective Q split i hV m μ hB hm hmpos).comp
    (suzukiActorEquiv Q split i m μ hB).symm.injective

include hB in
theorem derivedRadical_frattini_finrank_ge (hm : rotationOrder Q = 8) (hmpos : 0 < m) :
    4*(2*m+1) ≤ Module.finrank (ZMod 2)
      (Additive (derivedRadicalSection Q split i hV).EffectiveCarrier) := by
  exact Representation.Suzuki.finrank_ge hmpos
    (suzukiDerivedRepresentation Q split i hV m μ hB)
    (suzukiDerivedRepresentation_injective Q split i hV m μ hB hm hmpos)

include hV hB in
theorem derivedRadical_frattini_card_ge (hm : rotationOrder Q = 8) (hmpos : 0 < m) :
    (2^(2*m+1))^4 ≤ Nat.card
      ((⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) ⧸
        frattini (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))) := by
  let d := derivedRadicalSection Q split i hV
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.EffectiveCarrier)
  rw [Nat.card_zmod] at he
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2)
    (derivedRadical_frattini_finrank_ge Q split i hV m μ hB hm hmpos)
  rw [←he] at hh
  have hd : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]; exact sup_bot_eq _
  have hh' : (2^(2*m+1))^4 ≤ Nat.card d.EffectiveCarrier := by
    simpa only [pow_mul,Nat.mul_comm 4 (2*m+1),
      Nat.card_congr (Additive.toMul : Additive d.EffectiveCarrier ≃ _)] using hh
  change _ ≤ Nat.card (d.numerator ⧸ frattini d.numerator)
  change _ ≤ Nat.card (d.numerator ⧸ d.effectiveDenominator) at hh'
  rwa [hd] at hh'

include hV hB in
/-- The two effective source sections bound the next Frattini layer without identifying the fields. -/
theorem suzuki_derived_frattini_weighted_card_le
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hmpos : 0 < m) (j : Fin 2) (hij : i ≠ j) :
    Nat.card (frattini (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
      Subgroup (X ⧸ Q.D))) * (2^(2*m+1))^2 ≤ Nat.card (simpleRoot Q split j)^4 := by
  let V := simpleRemainder Q split i
  let D : Subgroup (X ⧸ Q.D) := ⁅V,V⁆
  let q := 2^(2*m+1)
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  have hDc : Nat.card D = Nat.card (commutator V) := by
    rw [show D = (commutator V).map V.subtype from (map_subtype_commutator V).symm,
      card_map_of_injective V.subtype_injective]
  have hD : Nat.card D ≤ q^2*Nat.card (simpleRoot Q split j)^4 := by
    rw [hDc]
    exact (Nat.le_of_dvd Nat.card_pos
      (card_dvd_of_le (commutator_le_frattini_of_isPGroup (p := 2)))).trans
      (suzuki_radical_frattini_card_le Q split i j m μ hB hV hc hm hij)
  have hquot : q^4 ≤ Nat.card (D ⧸ frattini D) :=
    derivedRadical_frattini_card_ge Q split i hV m μ hB hm hmpos
  have he := (frattini D).card_mul_index
  change Nat.card (frattini D) * Nat.card (D ⧸ frattini D) = Nat.card D at he
  have hh : (Nat.card (frattini D)*q^2)*q^2 ≤ Nat.card (simpleRoot Q split j)^4*q^2 := by
    calc
      _ = Nat.card (frattini D)*q^4 := by ring
      _ ≤ Nat.card (frattini D)*Nat.card (D ⧸ frattini D) := Nat.mul_le_mul_left _ hquot
      _ = Nat.card D := he
      _ ≤ q^2*Nat.card (simpleRoot Q split j)^4 := hD
      _ = _ := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right hh (by dsimp [q]; positivity)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
