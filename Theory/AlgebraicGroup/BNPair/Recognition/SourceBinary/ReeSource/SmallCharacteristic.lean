module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiSections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.BinaryCentralizers
public import Theory.Frattini.Intersection

/-!
# Small characteristic sections in the source octagon

The two faithful Frattini layers bound the order of the actual second
Frattini subgroup by less than q⁴ whenever |U_j|⁴ < q⁶. A nontrivial
positive-parameter Suzuki action on an invariant section would have an
effective quotient of order at least q⁴, so the whole source rank-one
actor centralizes this subgroup. For Sz(2), the quintic fixed-index bound
instead proves centralization by the actual order-five mover. Frattini
monotonicity gives the same control on Φ([V,V]).

These are literal subgroup centralizations in the given quotient. They do
not assert Φ²(V)=1 or centralization of an entire nonabelian Suzuki root.
They support the derived-section analysis on Fong--Seitz I (1973), pp.52--53,
following (6.4). The source SmallCharacteristic consumer discharges (6.3)
from the natural panel markings and retains both original endpoint maps.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

theorem positive_small_section_centralizes (m : ℕ) (hm : 0 < m)
    (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (d : RootSection Q split i) (hd : d.denominator = ⊥)
    (hsmall : Nat.card d.numerator < (2^(2*m+1))^4) :
    d.numerator ≤ centralizer (rankOne Q split i : Set (X ⧸ Q.D)) := by
  have hz : d.action = 1 := by
    by_contra hn
    have hlo := suzuki_section_card_bound Q split i hm μ d hn
    have hup := Nat.card_le_card_of_surjective (QuotientGroup.mk' d.effectiveDenominator)
      (QuotientGroup.mk'_surjective _)
    have hh : (2^(2*m+1))^4 ≤ Nat.card d.numerator := by
      simpa only [pow_mul,Nat.mul_comm 4 (2*m+1)] using hlo.trans hup
    exact hh.not_gt hsmall
  intro x hx
  apply mem_centralizer_iff.mpr
  intro r hr
  have he : d.numeratorAction ⟨r,hr⟩ ⟨x,hx⟩ = ⟨x,hx⟩ := by
    have hh : d.numeratorAction ⟨r,hr⟩ ⟨x,hx⟩ / ⟨x,hx⟩ ∈ d.denominator :=
      QuotientGroup.eq_iff_div_mem.mp ((d.action_mk ⟨r,hr⟩ ⟨x,hx⟩).symm.trans
        (by rw [hz]; rfl))
    rw [hd] at hh
    exact div_eq_one.mp (mem_bot.mp hh)
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)

theorem small_section_quintic_centralizes (d : RootSection Q split i)
    (hsmall : Nat.card d.numerator < 16)
    (c : rankOne Q split i) (hc : c^5 = 1) :
    d.numerator ≤ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) := by
  have hz : d.numeratorAction c = 1 := by
    by_contra hn
    have hlo := quintic_fixed_index_ge d.isTwo (d.numeratorAction c)
      (by rw [←map_pow,hc,map_one]) hn
    have hup := Nat.card_le_card_of_surjective
      (Quotient.mk _ : d.numerator → d.numerator ⧸ (d.numeratorAction c).fixedSubgroup)
      Quotient.mk_surjective
    exact (hlo.trans hup).not_gt hsmall
  intro x hx
  apply mem_centralizer_iff.mpr
  rintro r (rfl : r = c)
  have he := congrArg (fun f : MulAut d.numerator => (f ⟨x,hx⟩ : X ⧸ Q.D)) hz
  exact mul_inv_eq_iff_eq_mul.mp he

variable (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include hB in
theorem secondFrattini_card_lt
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hsize : Nat.card (simpleRoot Q split j)^4 < (2^(2*m+1))^6) :
    Nat.card (secondFrattiniRadicalSection Q split i hV).numerator < (2^(2*m+1))^4 := by
  let f := frattiniRadicalSection Q split i hV
  let d := secondFrattiniRadicalSection Q split i hV
  have heq : Nat.card d.numerator = Nat.card (frattini (frattini (simpleRemainder Q split i))) := by
    change Nat.card ((frattini f.numerator).map f.numerator.subtype) = _
    rw [card_map_of_injective f.numerator.subtype_injective]
    let b : frattini (simpleRemainder Q split i) ≃* f.numerator :=
      (frattini (simpleRemainder Q split i)).equivMapOfInjective
        (simpleRemainder Q split i).subtype (simpleRemainder Q split i).subtype_injective
    rw [←frattini_map_equiv b,card_map_of_injective b.injective]
  have hh := (suzuki_frattini_frattini_weighted_card_le Q split i hV m μ hB hc hm j hij hcomm).trans_lt hsize
  rw [←heq,show (2^(2*m+1))^6 = (2^(2*m+1))^4*(2^(2*m+1))^2 by ring] at hh
  exact Nat.lt_of_mul_lt_mul_right hh

/-- The derived subgroup contributes no larger second layer than the Frattini subgroup. -/
theorem derived_frattini_le_secondFrattini :
    (frattini (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))).map
      (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)).subtype ≤
      (secondFrattiniRadicalSection Q split i hV).numerator := by
  let V := simpleRemainder Q split i
  let f := frattiniRadicalSection Q split i hV
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  have hD : ⁅V,V⁆ ≤ f.numerator := by
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  exact frattini_image_le_of_le hD f.isTwo

include hB in
/-- The whole positive-parameter rank-one group fixes the small second Frattini subgroup. -/
theorem positive_secondFrattini_centralizes (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hsize : Nat.card (simpleRoot Q split j)^4 < (2^(2*m+1))^6) :
    (secondFrattiniRadicalSection Q split i hV).numerator ≤
      centralizer (rankOne Q split i : Set (X ⧸ Q.D)) :=
  positive_small_section_centralizes Q split i m hmpos (suzukiActorEquiv Q split i m μ hB)
    (secondFrattiniRadicalSection Q split i hV) rfl
    (secondFrattini_card_lt Q split i hV m μ hB hc hm j hij hcomm hsize)

omit m μ hB in
/-- In the binary row, the actual order-five mover fixes the same second Frattini subgroup. -/
theorem binary_secondFrattini_centralizes
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hsize : Nat.card (simpleRoot Q split j)^4 < 64) :
    (secondFrattiniRadicalSection Q split i hV).numerator ≤
      centralizer ({(frattiniMover Q split i 0 μ hB : X ⧸ Q.D)} : Set (X ⧸ Q.D)) := by
  apply small_section_quintic_centralizes Q split i (secondFrattiniRadicalSection Q split i hV)
  · simpa using secondFrattini_card_lt Q split i hV 0 μ hB hc hm j hij hcomm (by simpa using hsize)
  · rw [←binary_frattiniMover_order Q split i hV μ hB hm j hij hcomm,pow_orderOf_eq_one]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
