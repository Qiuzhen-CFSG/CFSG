module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PositiveFixedBounds
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.BinaryRadicalBounds

/-!
# The positive-parameter source centralizer estimates (6.1)

Write V for the actual endpoint radical and q for the Suzuki field order.
The two faithful Frattini layers have order at least q⁴. The octagon order
formula and |U_j| ≤ q bound each layer above by q⁶. PositiveFixedBounds
therefore applies to both of their literal actions. Multiplying their fixed
indices gives index at least q⁶ for the marked order-four root element and
q⁴ for its square on the whole V. The square lies in Ω₁(U_i), giving
|C_V(U_i)| ≤ |U_j|⁴ and |C_V(Ω₁(U_i))| ≤ q² |U_j|⁴.

No equality Φ(V)=[V,V] or natural identification of the entire layers is
used. The size comparison and local-characteristic-two premise are explicit.
OriginalSixOne supplies the natural panel markings, source (6.3), original
endpoint self-centralization, and the literal Q.q consumer. Its common-field
specialization derives the size comparison while retaining odd linear degree.

Source: Fong--Seitz I (1973), proof of (6H), printed p.52, equation (6.1).
The binary parameter is covered separately by BinaryRadicalBounds.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include hB in
/-- Both actual Frattini layers have order at most q⁶ under the source size comparison. -/
theorem radical_two_layers_card_le
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hsize : Nat.card (simpleRoot Q split j) ≤ 2^(2*m+1)) :
    Nat.card ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)) ≤ (2^(2*m+1))^6 ∧
    Nat.card ((frattiniRadicalSection Q split i hV).numerator ⧸
      frattini (frattiniRadicalSection Q split i hV).numerator) ≤ (2^(2*m+1))^6 := by
  let V := simpleRemainder Q split i
  let f := frattiniRadicalSection Q split i hV
  let q := 2^(2*m+1)
  have hfc : Nat.card f.numerator = Nat.card (frattini V) :=
    card_map_of_injective V.subtype_injective
  have hquot := frattiniRadical_frattini_card_ge Q split i hV m μ hB hm j hij hcomm
  have hquotle : Nat.card (f.numerator ⧸ frattini f.numerator) ≤ Nat.card f.numerator :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hlo : q^4 ≤ Nat.card (frattini V) := by
    rw [←hfc]
    exact hquot.trans hquotle
  have hup : Nat.card (frattini V) ≤ q^6 := by
    calc
      _ ≤ q^2*Nat.card (simpleRoot Q split j)^4 :=
        suzuki_radical_frattini_card_le Q split i j m μ hB hV hc hm hij
      _ ≤ q^2*q^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 4)
      _ = _ := by ring
  refine ⟨?_,hquotle.trans (hfc ▸ hup)⟩
  have hv : Nat.card V ≤ q^10 := by
    calc
      _ = q^6*Nat.card (simpleRoot Q split j)^4 :=
        suzuki_octagon_radical_card Q split i j m μ hB hm hij
      _ ≤ q^6*q^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 4)
      _ = _ := by ring
  have he := (frattini V).index_mul_card
  change Nat.card (V ⧸ frattini V)*Nat.card (frattini V) = Nat.card V at he
  have hh : Nat.card (V ⧸ frattini V)*q^4 ≤ q^6*q^4 := by
    calc
      _ ≤ Nat.card (V ⧸ frattini V)*Nat.card (frattini V) := Nat.mul_le_mul_left _ hlo
      _ = Nat.card V := he
      _ ≤ q^10 := hv
      _ = q^6*q^4 := by ring
  exact Nat.le_of_mul_le_mul_right hh (by dsimp [q]; positivity)

include hB in
/-- The marked order-four element has the two source fixed-index bounds on the whole radical. -/
theorem positive_radical_four_fixed_cards
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j) (hmpos : 0 < m)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hsize : Nat.card (simpleRoot Q split j) ≤ 2^(2*m+1)) :
    let r : rankOne Q split i := inclusion le_sup_left (suzukiParameter Q split i m μ hB 1 0)
    Nat.card ((radicalSection Q split i hV).numeratorAction r).fixedSubgroup * (2^(2*m+1))^6 ≤
        Nat.card (simpleRemainder Q split i) ∧
    Nat.card ((radicalSection Q split i hV).numeratorAction (r^2)).fixedSubgroup * (2^(2*m+1))^4 ≤
        Nat.card (simpleRemainder Q split i) := by
  dsimp only
  let d := radicalSection Q split i hV
  let f := frattiniRadicalSection Q split i hV
  let r : rankOne Q split i := inclusion le_sup_left (suzukiParameter Q split i m μ hB 1 0)
  have hb := radical_two_layers_card_le Q split i hV m μ hB hc hm j hij hcomm hsize
  have h1 := positive_section_fixed_indices Q split i m μ hB hmpos d rfl
    (radical_effectiveAction_injective Q split i hV hc) hb.1
  have h2 := positive_section_fixed_indices Q split i m μ hB hmpos f rfl
    (frattiniRadical_effectiveAction_injective Q split i hV m μ hB hm j hij hcomm) hb.2
  have hsur (x : rankOne Q split i) :
      (quotientAut (frattini f.numerator) (f.numeratorAction x)).fixedSubgroup.index ≤
      (f.numeratorAction x).fixedSubgroup.index :=
    fixed_index_le_of_surjective _ _ (QuotientGroup.mk' (frattini f.numerator))
      (QuotientGroup.mk'_surjective _) (fun _ => (quotientAut_apply_mk _ _ _).symm)
  have h2r := h2.1.trans (hsur r)
  have h2s := h2.2.trans (hsur (r^2))
  let e : frattini d.numerator ≃* f.numerator :=
    (frattini d.numerator).equivMapOfInjective d.numerator.subtype d.numerator.subtype_injective
  have he (x : rankOne Q split i) :
      (MulAut.characteristic (frattini d.numerator) (d.numeratorAction x)).fixedSubgroup.index =
        (f.numeratorAction x).fixedSubgroup.index := by
    apply fixed_index_eq_of_equivariant _ _ e
    intro v
    apply Subtype.ext
    rfl
  rw [←he] at h2r h2s
  have hh1 := fixed_card_mul_indices_le (frattini d.numerator) (d.numeratorAction r)
    _ _ h1.1 h2r
  have hh2 := fixed_card_mul_indices_le (frattini d.numerator) (d.numeratorAction (r^2))
    _ _ h1.2 h2s
  rw [←pow_add] at hh1 hh2
  exact ⟨hh1,hh2⟩

include hV hB in
/-- Both positive-parameter whole-radical bounds (6.1), with the field-size comparison explicit. -/
theorem positive_source_six_one
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j) (hmpos : 0 < m)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hsize : Nat.card (simpleRoot Q split j) ≤ 2^(2*m+1)) :
    Nat.card (simpleRemainder Q split i ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) :
        Subgroup (X ⧸ Q.D)) ≤ Nat.card (simpleRoot Q split j)^4 ∧
    Nat.card (simpleRemainder Q split i ⊓
      centralizer (omegaOneAmbient (simpleRoot Q split i) : Set (X ⧸ Q.D)) :
        Subgroup (X ⧸ Q.D)) ≤ (2^(2*m+1))^2*Nat.card (simpleRoot Q split j)^4 := by
  let d := radicalSection Q split i hV
  let u := suzukiParameter Q split i m μ hB 1 0
  let r : rankOne Q split i := inclusion le_sup_left u
  let q := 2^(2*m+1)
  obtain ⟨h1,h2⟩ := positive_radical_four_fixed_cards Q split i hV m μ hB hc hm j hij hmpos hcomm hsize
  change Nat.card (d.numeratorAction r).fixedSubgroup*q^6 ≤ Nat.card d.numerator at h1
  change Nat.card (d.numeratorAction (r^2)).fixedSubgroup*q^4 ≤ Nat.card d.numerator at h2
  rw [Nat.card_congr (radicalFixedEquiv Q split i hV r).toEquiv] at h1
  rw [Nat.card_congr (radicalFixedEquiv Q split i hV (r^2)).toEquiv] at h2
  have hr : r^4=1 := by
    apply Subtype.ext
    change (u : X ⧸ Q.D)^4=1
    exact congrArg Subtype.val (show u^4=1 by
      rw [←suzukiParameter_generator_order Q split i m μ hB,pow_orderOf_eq_one])
  have hroot : (r : X ⧸ Q.D) ∈ simpleRoot Q split i := u.property
  have homega : ((r^2 : rankOne Q split i) : X ⧸ Q.D) ∈ omegaOneAmbient (simpleRoot Q split i) := by
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl _ ((simpleRoot Q split i).pow_mem hroot 2)
    rw [←pow_mul]
    exact congrArg Subtype.val hr
  have hc1 := card_le_of_le (show
      simpleRemainder Q split i ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) ≤
        simpleRemainder Q split i ⊓ centralizer ({(r : X ⧸ Q.D)} : Set _) from
    inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hroot)))
  have hc2 := card_le_of_le (show
      simpleRemainder Q split i ⊓ centralizer (omegaOneAmbient (simpleRoot Q split i) : Set (X ⧸ Q.D)) ≤
        simpleRemainder Q split i ⊓ centralizer ({((r^2 : rankOne Q split i) : X ⧸ Q.D)} : Set _) from
    inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr homega)))
  have hv := suzuki_octagon_radical_card Q split i j m μ hB hm hij
  change Nat.card d.numerator = q^6*Nat.card (simpleRoot Q split j)^4 at hv
  rw [hv] at h1 h2
  constructor
  · exact hc1.trans (Nat.le_of_mul_le_mul_right (h1.trans_eq (Nat.mul_comm _ _)) (by dsimp [q]; positivity))
  · have hh : Nat.card (simpleRemainder Q split i ⊓ centralizer ({((r^2 : rankOne Q split i) : X ⧸ Q.D)} : Set _) : Subgroup (X ⧸ Q.D)) * q^4 ≤
        (q^2*Nat.card (simpleRoot Q split j)^4)*q^4 := by
      calc
        _ ≤ q^6*Nat.card (simpleRoot Q split j)^4 := h2
        _ = _ := by ring
    exact hc2.trans (Nat.le_of_mul_le_mul_right hh (by dsimp [q]; positivity))

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
