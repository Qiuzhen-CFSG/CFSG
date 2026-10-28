module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FrattiniRadical

/-!
# Frattini support on a product of adjacent source roots

A nonidentity element of the shifted Suzuki root in Φ²(V) is moved by
an order-five actor when m=0 and by a nontrivial Suzuki actor when m>0.
The resulting third effective section forces q_Suz⁶ ≤ |U_j|⁴. This uses
actual conjugation on the same octagonal quotient and the previously
proved all-parameter Frattini bounds.

For a commuting product ab in Φ(V), with a in that root and b²=1, its
square is a² and belongs to Φ²(V). Thus |U_j|⁴ < q_Suz⁶ forces (ab)²=1
and a in the actual Omega root. Crucially, neither a nor b is assumed to
lie in Φ(V). The source ProductSupport consumer supplies the adjacent
linear root, commutation, exponent two and (6.3) from natural markings.

Source: Fong--Seitz I (1973), proof of (6H), printed p.52, the product
order-four obstruction immediately before (6.4). This is the product
support step; removing the remaining linear factor and proving the full
mixed-commutator equality require further source arguments.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped Pointwise IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)
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


include hV hB in
theorem secondFrattini_shifted_root_forces_card
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (a : rootAt Q split i (Q.simple j*Q.simple i))
    (ha : (a : X ⧸ Q.D) ∈ (secondFrattiniRadicalSection Q split i hV).numerator)
    (han : (a : X ⧸ Q.D) ≠ 1) :
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
    let v : d.numerator := ⟨a,ha⟩
    have huΩ : (u : X ⧸ Q.D) ∈ omegaOneAmbient (simpleRoot Q split i) := by
      rw [←suzukiOmegaParameter_range Q split i m μ hB]
      exact ⟨Multiplicative.ofAdd 1,rfl⟩
    have huc : Commute (u : X ⧸ Q.D) (v : X ⧸ Q.D) :=
      (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm huΩ) _
        a.property).symm
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
      exact a.property
    exact han (disjoint_def.mp hAB a.property hvB)
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


include hV hB in
/-- If a commuting two-root product in Φ(V) has nontrivial square, then
its square supplies the third effective Suzuki layer. Neither factor is
assumed to lie in Φ(V). -/
theorem frattini_product_order_four_forces_card
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (a : rootAt Q split i (Q.simple j*Q.simple i)) (b : X ⧸ Q.D)
    (hab : Commute (a : X ⧸ Q.D) b) (hb : b^2 = 1)
    (hz : (a : X ⧸ Q.D)*b ∈ (frattiniRadicalSection Q split i hV).numerator)
    (hn : ((a : X ⧸ Q.D)*b)^2 ≠ 1) :
    (2^(2*m+1))^6 ≤ Nat.card (simpleRoot Q split j)^4 := by
  let f := frattiniRadicalSection Q split i hV
  let d := secondFrattiniRadicalSection Q split i hV
  let : Fact (IsPGroup 2 f.numerator) := ⟨f.isTwo⟩
  let z : f.numerator := ⟨(a : X ⧸ Q.D)*b,hz⟩
  have hs : ((a : X ⧸ Q.D)*b)^2 = (a : X ⧸ Q.D)^2 := by
    rw [hab.mul_pow,hb,mul_one]
  have hz2 : ((a : X ⧸ Q.D)*b)^2 ∈ d.numerator :=
    ⟨z^2,pth_power_mem_frattini_of_isPGroup (p := 2) z,rfl⟩
  rw [hs] at hz2 hn
  exact secondFrattini_shifted_root_forces_card Q split i hV m μ hB hc hm j hij hcomm
    (a^2) hz2 hn

include hV hB in
/-- Product support in Φ(V), with the independent-field size obstruction explicit. -/
theorem frattini_product_support
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hsize : Nat.card (simpleRoot Q split j)^4 < (2^(2*m+1))^6)
    (B : Subgroup (X ⧸ Q.D))
    (hAB : ⁅rootAt Q split i (Q.simple j*Q.simple i),B⁆ = ⊥)
    (hB2 : ∀ b ∈ B, b^2 = 1) (z : X ⧸ Q.D)
    (hz : z ∈ (frattiniRadicalSection Q split i hV).numerator)
    (hp : z ∈ (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) * (B : Set (X ⧸ Q.D))) :
    z^2 = 1 ∧ z ∈ (omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)) : Set (X ⧸ Q.D)) * (B : Set (X ⧸ Q.D)) := by
  obtain ⟨a,ha,b,hb,rfl⟩ := hp
  have hab : Commute a b :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hAB ha) b hb).symm
  have hs : (a*b)^2 = 1 := by
    by_contra hn
    exact (frattini_product_order_four_forces_card Q split i hV m μ hB hc hm j hij hcomm
      ⟨a,ha⟩ b hab (hB2 b hb) hz hn).not_gt hsize
  refine ⟨hs,a,?_,b,hb,rfl⟩
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl a ha
  simpa only [hab.mul_pow,hB2 b hb,mul_one] using hs

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
