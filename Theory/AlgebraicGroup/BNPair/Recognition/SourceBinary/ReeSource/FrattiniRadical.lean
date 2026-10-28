module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.BinarySections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.DerivedRadical
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The effective Frattini radical for every Suzuki parameter

Set V = U ∩ U^s on the same octagonal quotient. A shifted Suzuki root
lies in V and has an element of order four; its nonidentity square lies
in Φ(V). The central simple-root involution fixes this square by (6.3),
while the actual root reflection sends its root to a disjoint root.
Their product therefore moves Φ(V). At parameter zero this product has
order five, so BinarySections proves effective faithfulness without
simplicity. At positive parameters simplicity and the two-group kernel
of the Frattini action give the same conclusion.

The actual Φ(V)/Φ(Φ(V)) action consequently has binary dimension at least
4(2m+1), including m=0. Combined with the full-radical bound this proves
|Φ(Φ(V))| q_Suz² ≤ |U_j|⁴ before field synchronization. The (6.3) input
is discharged by the natural-panel source consumer in OriginalFrattiniRadical;
no action, natural-module identification or common field is assumed.

An order-four element in the indicated shifted root inside Φ(V) would
repeat the argument on Φ²(V), forcing q_Suz⁶ ≤ |U_j|⁴. The original
consumer uses the existing common-field theorem to exclude it, retaining
that theorem's explicit odd-linear-degree input.

Source: Fong--Seitz I (1973), (5D) and the effective-section argument in
(6H), pp.26--27,52--53. This Frattini-section estimate does not identify
Φ(V) with [V,V], prove (6.1)/(6.4), or prove the mixed-commutator equality.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)

def frattiniRadicalSection : RootSection Q split i where
  numerator := (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype
  le_radical := map_subtype_le _
  normalized := ((rankOne_le_parabolic Q split i).trans
    (remainder_parabolic_normalizes Q split i hV)).trans
      (normalizer_le_normalizer_characteristic_image _ _)
  denominator := ⊥
  invariant _ := Subgroup.map_bot _

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

variable (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

/-- The actual corrected reflection and the central root involution. -/
def frattiniMover : rankOne Q split i :=
  let s := involutoryRootReflection Q split i (UnitarySource.actorReflection Q split i)
  ⟨s.val,s.mem_rankOne⟩ * inclusion le_sup_left (suzukiParameter Q split i m μ hB 0 1)

include hB in
theorem frattiniMover_moves (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    (frattiniRadicalSection Q split i hV).action (frattiniMover Q split i m μ hB) ≠ 1 := by
  let s := involutoryRootReflection Q split i (UnitarySource.actorReflection Q split i)
  let u : rankOne Q split i := inclusion le_sup_left (suzukiParameter Q split i m μ hB 0 1)
  let A := rootAt Q split i (Q.simple j*Q.simple i)
  let B := rootAt Q split i (Q.simple j)
  have hi := octagon_lengths Q i hm j hij
  have hj := octagon_lengths Q j hm i hij.symm
  have hs (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2)
  have hss (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
  have hAV : A ≤ simpleRemainder Q split i := by
    apply rootAt_le_remainder Q split i i (Q.simple j*Q.simple i)
    · rw [mul_inv_rev,hs,hs,hi.2.2.1,hi.2.1]
    · simp only [mul_inv_rev,hs,← mul_assoc,hss,one_mul]
      rw [hj.2.1,hj.1]
  have hAB : Disjoint A B := by
    apply Disjoint.symm
    apply rootAt_disjoint Q split i (Q.simple j) (Q.simple j*Q.simple i)
    simp only [mul_inv_rev,hs,←mul_assoc]
    rw [hi.2.2.2.2,hi.2.2.2.1]
  let a : A := (RootAction.conjugateEquiv (simpleRoot Q split i)
    (representative (Q.simple j*Q.simple i))).symm (suzukiParameter Q split i m μ hB 1 0)
  have haorder : orderOf a = 4 := by
    change orderOf ((RootAction.conjugateEquiv (simpleRoot Q split i)
      (representative (Q.simple j*Q.simple i))).symm (suzukiParameter Q split i m μ hB 1 0)) = 4
    rw [MulEquiv.orderOf_eq,suzukiParameter_generator_order]
  have han : (a : X ⧸ Q.D)^2 ≠ 1 := by
    intro hz
    have hh : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext hz)
    rw [haorder] at hh
    norm_num at hh
  let d := frattiniRadicalSection Q split i hV
  let : Fact (IsPGroup 2 (simpleRemainder Q split i)) := ⟨split.isTwo.to_le inf_le_left⟩
  let v : d.numerator := ⟨(a : X ⧸ Q.D)^2,
    ⟨(⟨a,hAV a.property⟩ : simpleRemainder Q split i)^2,
      pth_power_mem_frattini_of_isPGroup (p := 2) _,rfl⟩⟩
  have huΩ : (u : X ⧸ Q.D) ∈ omegaOneAmbient (simpleRoot Q split i) := by
    rw [←suzukiOmegaParameter_range Q split i m μ hB]
    exact ⟨Multiplicative.ofAdd 1,rfl⟩
  have huc : Commute (u : X ⧸ Q.D) (v : X ⧸ Q.D) :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm huΩ) _
      (A.pow_mem a.property 2)).symm
  intro he
  have hv : d.numeratorAction (frattiniMover Q split i m μ hB) v = v := by
    have hh := congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk v)) he
    rw [d.action_mk] at hh
    exact congrArg QuotientGroup.quotientBot hh
  have hfix : (s.val : X ⧸ Q.D)*(v : X ⧸ Q.D)*(s.val : X ⧸ Q.D)⁻¹ = v := by
    have hh := congrArg (fun z : d.numerator => (z : X ⧸ Q.D)) hv
    change ((s.val : X ⧸ Q.D)*(u : X ⧸ Q.D))*(v : X ⧸ Q.D)*
      ((s.val : X ⧸ Q.D)*(u : X ⧸ Q.D))⁻¹ = v at hh
    calc
      _ = (s.val : X ⧸ Q.D)*((u : X ⧸ Q.D)*(v : X ⧸ Q.D)*(u : X ⧸ Q.D)⁻¹)*
        (s.val : X ⧸ Q.D)⁻¹ := by rw [huc.eq,mul_inv_cancel_right]
      _ = _ := by simpa only [mul_inv_rev,mul_assoc] using hh
  have hBA : rightConjugate A (s.val : X ⧸ Q.D) = B := by
    rw [rootAt_right Q split i (Q.simple j*Q.simple i) (Q.simple i) s.val s.class_eq,
      mul_assoc,hss,mul_one]
  have hvB : (v : X ⧸ Q.D) ∈ B := by
    rw [←hBA]
    change (s.val : X ⧸ Q.D)*(v : X ⧸ Q.D)*(s.val : X ⧸ Q.D)⁻¹ ∈ A
    rw [hfix]
    exact A.pow_mem a.property 2
  exact han (disjoint_def.mp hAB (A.pow_mem a.property 2) hvB)


variable (μ₀ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB₀ : (quotientBorel Q i).map μ₀.toMonoidHom =
    normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

include hV hB₀ in
theorem binary_frattiniMover_order (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    orderOf (frattiniMover Q split i 0 μ₀ hB₀) = 5 := by
  let s := involutoryRootReflection Q split i (UnitarySource.actorReflection Q split i)
  let r : rankOne Q split i := ⟨s.val,s.mem_rankOne⟩
  let u : rankOne Q split i := inclusion le_sup_left (suzukiParameter Q split i 0 μ₀ hB₀ 0 1)
  have hr2 : r^2 = 1 := Subtype.ext
    (involutoryRootReflection_sq Q split i (UnitarySource.actorReflection Q split i))
  have hrn : r ≠ 1 := fun he => involutoryRootReflection_ne_one Q split i
    (UnitarySource.actorReflection Q split i) (congrArg Subtype.val he)
  have hu2 : u^2 = 1 := by
    apply Subtype.ext
    change ((suzukiParameter Q split i 0 μ₀ hB₀ 0 1)^2 : simpleRoot Q split i).val = 1
    rw [suzukiParameter_square,zero_mul,suzukiParameter_zero]
    rfl
  have hun : u ≠ 1 := by
    intro he
    have hh : suzukiParameter Q split i 0 μ₀ hB₀ 0 1 = 1 :=
      Subtype.ext (congrArg (fun z : rankOne Q split i => (z : X ⧸ Q.D)) he)
    exact one_ne_zero ((suzukiParameter_eq_one_iff Q split i 0 μ₀ hB₀ 0 1).mp hh).2
  have hne : r ≠ u := by
    intro he
    have hmove := frattiniMover_moves Q split i hV 0 μ₀ hB₀ hm j hij hcomm
    apply hmove
    have hz : frattiniMover Q split i 0 μ₀ hB₀ = 1 := by
      change r*u = 1
      rw [he,←pow_two,hu2]
    rw [hz,map_one]
  let e := suzukiActorEquiv Q split i 0 μ₀ hB₀
  have hh := binary_suzuki_involution_product_order (e r) (e u)
    (by rw [←map_pow,hr2,map_one]) (e.map_ne_one_iff.mpr hrn)
    (by rw [←map_pow,hu2,map_one]) (e.map_ne_one_iff.mpr hun)
    (fun he => hne (e.injective he))
  rw [←map_mul,e.orderOf_eq] at hh
  exact hh

include hB in
private theorem positive_suzuki_section_effective (d : RootSection Q split i)
    (hdenom : d.denominator = ⊥) (hmpos : 0 < m)
    (hmove : d.action (frattiniMover Q split i m μ hB) ≠ 1) :
    Function.Injective d.effectiveAction := by
  let e := suzukiActorEquiv Q split i m μ hB
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hmpos).1
  let : IsSimpleGroup (rankOne Q split i) := e.isSimpleGroup
  have hnum : Function.Injective d.numeratorAction := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases (inferInstance : d.numeratorAction.ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    have hz := MonoidHom.ker_eq_top_iff.mp ht
    apply hmove.elim
    ext z
    induction z using QuotientGroup.induction_on with
    | H v =>
      rw [d.action_mk]
      have he := congrArg (fun f : rankOne Q split i →* MulAut d.numerator =>
        f (frattiniMover Q split i m μ hB) v) hz
      change d.numeratorAction (frattiniMover Q split i m μ hB) v = v at he
      rw [he]
      rfl
  let a := (quotientAut (frattini d.numerator)).comp d.numeratorAction
  have htwo : IsPGroup 2 a.ker :=
    (isPGroup_quotientAut_frattini_kernel d.isTwo).comap_of_injective d.numeratorAction hnum
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
    rw [d.effectiveDenominator_eq,hdenom,sup_bot_eq]
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
theorem frattiniRadical_effectiveAction_injective (hm : rotationOrder Q = 8)
    (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    Function.Injective (frattiniRadicalSection Q split i hV).effectiveAction := by
  by_cases hm0 : m = 0
  · subst m
    exact binary_suzuki_section_effectiveAction_injective Q split i μ hB _ _
      (binary_frattiniMover_order Q split i hV μ hB hm j hij hcomm)
      (frattiniMover_moves Q split i hV 0 μ hB hm j hij hcomm)
  exact positive_suzuki_section_effective Q split i m μ hB _ rfl (by omega)
    (frattiniMover_moves Q split i hV m μ hB hm j hij hcomm)

/-- The Suzuki representation is transported from this exact source section. -/
def suzukiFrattiniRadicalRepresentation : Representation (ZMod 2) (SuzukiMatrixGroup m)
    (Additive (frattiniRadicalSection Q split i hV).EffectiveCarrier) :=
  (frattiniRadicalSection Q split i hV).effectiveRepresentation.comp
    (suzukiActorEquiv Q split i m μ hB).symm.toMonoidHom

@[simp] theorem suzukiFrattiniRadicalRepresentation_source
    (r : rankOne Q split i) (x : (frattiniRadicalSection Q split i hV).numerator) :
    suzukiFrattiniRadicalRepresentation Q split i hV m μ hB (suzukiActorEquiv Q split i m μ hB r)
      (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk
        ((frattiniRadicalSection Q split i hV).numeratorAction r x)) := by
  change (frattiniRadicalSection Q split i hV).effectiveRepresentation
    ((suzukiActorEquiv Q split i m μ hB).symm (suzukiActorEquiv Q split i m μ hB r)) _ = _
  rw [MulEquiv.symm_apply_apply,RootSection.effectiveRepresentation_mk]

include hB in
theorem suzukiFrattiniRadicalRepresentation_injective (hm : rotationOrder Q = 8)
    (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    Function.Injective (suzukiFrattiniRadicalRepresentation Q split i hV m μ hB) :=
  ((frattiniRadicalSection Q split i hV).effectiveRepresentation_injective
    (frattiniRadical_effectiveAction_injective Q split i hV m μ hB hm j hij hcomm)).comp
      (suzukiActorEquiv Q split i m μ hB).symm.injective

include hB in
theorem frattiniRadical_frattini_finrank_ge (hm : rotationOrder Q = 8)
    (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    4*(2*m+1) ≤ Module.finrank (ZMod 2)
      (Additive (frattiniRadicalSection Q split i hV).EffectiveCarrier) := by
  let ρ := suzukiFrattiniRadicalRepresentation Q split i hV m μ hB
  have hf := suzukiFrattiniRadicalRepresentation_injective Q split i hV m μ hB hm j hij hcomm
  by_cases hm0 : m = 0
  · subst m
    have hh := Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hf
      (by decide : Nat.Prime 5) (by decide : 5 ≠ 2)
      (show 5 ∣ Nat.card (SuzukiMatrixGroup 0) by rw [suzukiZero_card]; decide)
    simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_five, Nat.mul_zero,
      Nat.zero_add, Nat.mul_one] using hh
  · exact Representation.Suzuki.finrank_ge (by omega) ρ hf

include hB in
theorem frattiniRadical_frattini_card_ge (hm : rotationOrder Q = 8)
    (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    (2^(2*m+1))^4 ≤ Nat.card
      ((frattiniRadicalSection Q split i hV).numerator ⧸
        frattini (frattiniRadicalSection Q split i hV).numerator) := by
  let d := frattiniRadicalSection Q split i hV
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.EffectiveCarrier)
  rw [Nat.card_zmod] at he
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2)
    (frattiniRadical_frattini_finrank_ge Q split i hV m μ hB hm j hij hcomm)
  rw [←he] at hh
  have hd : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]; exact sup_bot_eq _
  have hh' : (2^(2*m+1))^4 ≤ Nat.card d.EffectiveCarrier := by
    simpa only [pow_mul,Nat.mul_comm 4 (2*m+1),
      Nat.card_congr (Additive.toMul : Additive d.EffectiveCarrier ≃ _)] using hh
  change _ ≤ Nat.card (d.numerator ⧸ d.effectiveDenominator) at hh'
  rwa [hd] at hh'

include hV hB in
/-- The next Frattini layer is bounded for all Suzuki parameters, with independent root orders. -/
theorem suzuki_frattini_frattini_weighted_card_le
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    Nat.card (frattini (frattini (simpleRemainder Q split i))) *
      (2^(2*m+1))^2 ≤ Nat.card (simpleRoot Q split j)^4 := by
  let V := simpleRemainder Q split i
  let D := (frattiniRadicalSection Q split i hV).numerator
  let q := 2^(2*m+1)
  let e : frattini V ≃* D := (frattini V).equivMapOfInjective V.subtype V.subtype_injective
  have hDc : Nat.card D = Nat.card (frattini V) := (Nat.card_congr e.toEquiv).symm
  have hφc : Nat.card (frattini D) = Nat.card (frattini (frattini V)) := by
    rw [←frattini_map_equiv e,card_map_of_injective e.injective]
  have hD : Nat.card D ≤ q^2*Nat.card (simpleRoot Q split j)^4 := by
    rw [hDc]
    exact suzuki_radical_frattini_card_le Q split i j m μ hB hV hc hm hij
  have hquot : q^4 ≤ Nat.card (D ⧸ frattini D) :=
    frattiniRadical_frattini_card_ge Q split i hV m μ hB hm j hij hcomm
  have he := (frattini D).card_mul_index
  change Nat.card (frattini D) * Nat.card (D ⧸ frattini D) = Nat.card D at he
  have hh : (Nat.card (frattini D)*q^2)*q^2 ≤ Nat.card (simpleRoot Q split j)^4*q^2 := by
    calc
      _ = Nat.card (frattini D)*q^4 := by ring
      _ ≤ Nat.card (frattini D)*Nat.card (D ⧸ frattini D) := Nat.mul_le_mul_left _ hquot
      _ = Nat.card D := he
      _ ≤ q^2*Nat.card (simpleRoot Q split j)^4 := hD
      _ = _ := Nat.mul_comm _ _
  rw [hφc] at hh
  exact Nat.le_of_mul_le_mul_right hh (by dsimp [q]; positivity)


/-- The actual second Frattini subgroup, embedded in the same radical. -/
def secondFrattiniRadicalSection : RootSection Q split i where
  numerator := (frattini (frattiniRadicalSection Q split i hV).numerator).map
    (frattiniRadicalSection Q split i hV).numerator.subtype
  le_radical := (map_subtype_le _).trans (frattiniRadicalSection Q split i hV).le_radical
  normalized := (frattiniRadicalSection Q split i hV).normalized.trans
    (normalizer_le_normalizer_characteristic_image _ _)
  denominator := ⊥
  invariant _ := Subgroup.map_bot _

include hV hB in
/-- An order-four element in the indicated root and Φ(V) forces a third
Suzuki degree contribution. This is the size obstruction used before (6.4). -/
theorem frattini_root_order_four_forces_card
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (a : rootAt Q split i (Q.simple j*Q.simple i))
    (ha : (a : X ⧸ Q.D) ∈ (frattiniRadicalSection Q split i hV).numerator)
    (han : (a : X ⧸ Q.D)^2 ≠ 1) :
    (2^(2*m+1))^6 ≤ Nat.card (simpleRoot Q split j)^4 := by
  let f := frattiniRadicalSection Q split i hV
  let d := secondFrattiniRadicalSection Q split i hV
  have hmove : d.action (frattiniMover Q split i m μ hB) ≠ 1 := by
    let s := involutoryRootReflection Q split i (UnitarySource.actorReflection Q split i)
    let u : rankOne Q split i := inclusion le_sup_left (suzukiParameter Q split i m μ hB 0 1)
    let A := rootAt Q split i (Q.simple j*Q.simple i)
    let B := rootAt Q split i (Q.simple j)
    have hi := octagon_lengths Q i hm j hij
    have hs (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2)
    have hss (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
      simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
    have hAB : Disjoint A B := by
      apply Disjoint.symm
      apply rootAt_disjoint Q split i (Q.simple j) (Q.simple j*Q.simple i)
      simp only [mul_inv_rev,hs,←mul_assoc]
      rw [hi.2.2.2.2,hi.2.2.2.1]
    let : Fact (IsPGroup 2 f.numerator) := ⟨f.isTwo⟩
    let v : d.numerator := ⟨(a : X ⧸ Q.D)^2,
      ⟨(⟨a,ha⟩ : f.numerator)^2,pth_power_mem_frattini_of_isPGroup (p := 2) _,rfl⟩⟩
    have huΩ : (u : X ⧸ Q.D) ∈ omegaOneAmbient (simpleRoot Q split i) := by
      rw [←suzukiOmegaParameter_range Q split i m μ hB]
      exact ⟨Multiplicative.ofAdd 1,rfl⟩
    have huc : Commute (u : X ⧸ Q.D) (v : X ⧸ Q.D) :=
      (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm huΩ) _
        (A.pow_mem a.property 2)).symm
    intro he
    have hv : d.numeratorAction (frattiniMover Q split i m μ hB) v = v := by
      have hh := congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk v)) he
      rw [d.action_mk] at hh
      exact congrArg QuotientGroup.quotientBot hh
    have hfix : (s.val : X ⧸ Q.D)*(v : X ⧸ Q.D)*(s.val : X ⧸ Q.D)⁻¹ = v := by
      have hh := congrArg (fun z : d.numerator => (z : X ⧸ Q.D)) hv
      change ((s.val : X ⧸ Q.D)*(u : X ⧸ Q.D))*(v : X ⧸ Q.D)*
        ((s.val : X ⧸ Q.D)*(u : X ⧸ Q.D))⁻¹ = v at hh
      calc
        _ = (s.val : X ⧸ Q.D)*((u : X ⧸ Q.D)*(v : X ⧸ Q.D)*(u : X ⧸ Q.D)⁻¹)*
          (s.val : X ⧸ Q.D)⁻¹ := by rw [huc.eq,mul_inv_cancel_right]
        _ = _ := by simpa only [mul_inv_rev,mul_assoc] using hh
    have hBA : rightConjugate A (s.val : X ⧸ Q.D) = B := by
      rw [rootAt_right Q split i (Q.simple j*Q.simple i) (Q.simple i) s.val s.class_eq,
        mul_assoc,hss,mul_one]
    have hvB : (v : X ⧸ Q.D) ∈ B := by
      rw [←hBA]
      change (s.val : X ⧸ Q.D)*(v : X ⧸ Q.D)*(s.val : X ⧸ Q.D)⁻¹ ∈ A
      rw [hfix]
      exact A.pow_mem a.property 2
    exact han (disjoint_def.mp hAB (A.pow_mem a.property 2) hvB)
  have hf : Function.Injective d.effectiveAction := by
    by_cases hm0 : m = 0
    · subst m
      exact binary_suzuki_section_effectiveAction_injective Q split i μ hB d _
        (binary_frattiniMover_order Q split i hV μ hB hm j hij hcomm) hmove
    · exact positive_suzuki_section_effective Q split i m μ hB d rfl (by omega) hmove
  let e := suzukiActorEquiv Q split i m μ hB
  let ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) (Additive d.EffectiveCarrier) :=
    d.effectiveRepresentation.comp e.symm.toMonoidHom
  have hρ : Function.Injective ρ :=
    (d.effectiveRepresentation_injective hf).comp e.symm.injective
  have hdim : 4*(2*m+1) ≤ Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) := by
    by_cases hm0 : m = 0
    · subst m
      have hh := Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hρ
        (by decide : Nat.Prime 5) (by decide : 5 ≠ 2)
        (show 5 ∣ Nat.card (SuzukiMatrixGroup 0) by rw [suzukiZero_card]; decide)
      simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_five, Nat.mul_zero,
        Nat.zero_add, Nat.mul_one] using hh
    · exact Representation.Suzuki.finrank_ge (by omega) ρ hρ
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.EffectiveCarrier)
  rw [Nat.card_zmod] at he
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hdim
  rw [←he] at hh
  have hlo : (2^(2*m+1))^4 ≤ Nat.card d.EffectiveCarrier := by
    simpa only [pow_mul,Nat.mul_comm 4 (2*m+1),
      Nat.card_congr (Additive.toMul : Additive d.EffectiveCarrier ≃ _)] using hh
  have hn := Nat.card_le_card_of_surjective (QuotientGroup.mk' d.effectiveDenominator)
    (QuotientGroup.mk'_surjective _)
  have heq : Nat.card d.numerator = Nat.card (frattini (frattini (simpleRemainder Q split i))) := by
    change Nat.card ((frattini f.numerator).map f.numerator.subtype) = _
    rw [card_map_of_injective f.numerator.subtype_injective]
    let b : frattini (simpleRemainder Q split i) ≃* f.numerator :=
      (frattini (simpleRemainder Q split i)).equivMapOfInjective
        (simpleRemainder Q split i).subtype (simpleRemainder Q split i).subtype_injective
    rw [←frattini_map_equiv b,card_map_of_injective b.injective]
  have hsmall := suzuki_frattini_frattini_weighted_card_le Q split i hV m μ hB hc hm j hij hcomm
  calc
    (2^(2*m+1))^6 = (2^(2*m+1))^4*(2^(2*m+1))^2 := by ring
    _ ≤ Nat.card (frattini (frattini (simpleRemainder Q split i)))*(2^(2*m+1))^2 :=
      Nat.mul_le_mul_right _ ((hlo.trans hn).trans_eq heq)
    _ ≤ _ := hsmall

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
