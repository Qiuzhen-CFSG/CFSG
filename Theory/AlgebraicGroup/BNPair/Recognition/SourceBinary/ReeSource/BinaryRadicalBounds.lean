module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.BinaryFixedBounds

/-!
# Binary whole-radical centralizer bounds in the source octagon

The actual rank-one actor is faithful on V/Φ(V) and Φ(V)/Φ²(V). An
order-four actor therefore has fixed index at least eight on both layers;
its square has fixed index at least four. Multiplying the two contributions
bounds fixed points on the whole V, without requiring Φ(V)=[V,V].

Apply this to the marked Suzuki root generator (1,0). Its square belongs
to the actual Omega root. The order formula |V|=64 |U_j|^4 gives
|C_V(U_i)| ≤ |U_j|^4 and |C_V(Ω₁(U_i))| ≤ 4 |U_j|^4. For a linear root
of order two these are exactly 16 and 64, the binary case of (6.1).

Source: Fong--Seitz I (1973), proof of (6H), printed p.52, equation (6.1).
The original endpoint application supplies local characteristic two and
(6.3) from its natural panel markings. Positive Suzuki parameters, product
support in (6.4), and the later mixed-commutator equality remain separate.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

private theorem quotient_fixed_index_le (d : RootSection Q split i) (r : rankOne Q split i) :
    (quotientAut (frattini d.numerator) (d.numeratorAction r)).fixedSubgroup.index ≤
      (d.numeratorAction r).fixedSubgroup.index :=
  fixed_index_le_of_surjective _ _ (QuotientGroup.mk' (frattini d.numerator))
    (QuotientGroup.mk'_surjective _) (fun _ => (quotientAut_apply_mk _ _ _).symm)

include hB in
/-- The two literal Frattini layers bound fixed points of every order-four source actor. -/
theorem binary_radical_four_fixed_cards
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (r : rankOne Q split i) (hr : orderOf r = 4) :
    Nat.card ((radicalSection Q split i hV).numeratorAction r).fixedSubgroup * 64 ≤
        Nat.card (simpleRemainder Q split i) ∧
      Nat.card ((radicalSection Q split i hV).numeratorAction (r^2)).fixedSubgroup * 16 ≤
        Nat.card (simpleRemainder Q split i) := by
  let d := radicalSection Q split i hV
  let f := frattiniRadicalSection Q split i hV
  have h1 := binary_section_fixed_indices Q split i μ hB d rfl
    (radical_effectiveAction_injective Q split i hV hc) r hr
  have h2 := binary_section_fixed_indices Q split i μ hB f rfl
    (frattiniRadical_effectiveAction_injective Q split i hV 0 μ hB hm j hij hcomm) r hr
  have h2r := h2.1.trans (quotient_fixed_index_le Q split i f r)
  have h2s := h2.2.trans (quotient_fixed_index_le Q split i f (r^2))
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
  exact ⟨fixed_card_mul_indices_le (frattini d.numerator) (d.numeratorAction r) 8 8 h1.1 h2r,
    fixed_card_mul_indices_le (frattini d.numerator) (d.numeratorAction (r^2)) 4 4 h1.2 h2s⟩

include hV hB in
/-- Both whole-radical centralizer estimates (6.1) in the binary Suzuki row,
with the other root order still independent. -/
theorem binary_source_six_one
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    Nat.card (simpleRemainder Q split i ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) :
        Subgroup (X ⧸ Q.D)) ≤ Nat.card (simpleRoot Q split j)^4 ∧
      Nat.card (simpleRemainder Q split i ⊓
        centralizer (omegaOneAmbient (simpleRoot Q split i) : Set (X ⧸ Q.D)) :
          Subgroup (X ⧸ Q.D)) ≤ 4*Nat.card (simpleRoot Q split j)^4 := by
  let d := radicalSection Q split i hV
  let u := suzukiParameter Q split i 0 μ hB 1 0
  let r : rankOne Q split i := inclusion le_sup_left u
  have hr : orderOf r = 4 :=
    (orderOf_injective (inclusion le_sup_left) (inclusion_injective _) u).trans
      (suzukiParameter_generator_order Q split i 0 μ hB)
  obtain ⟨h1,h2⟩ := binary_radical_four_fixed_cards Q split i hV μ hB hc hm j hij hcomm r hr
  rw [Nat.card_congr (radicalFixedEquiv Q split i hV r).toEquiv] at h1
  rw [Nat.card_congr (radicalFixedEquiv Q split i hV (r^2)).toEquiv] at h2
  have hroot : (r : X ⧸ Q.D) ∈ simpleRoot Q split i := u.property
  have homega : ((r^2 : rankOne Q split i) : X ⧸ Q.D) ∈ omegaOneAmbient (simpleRoot Q split i) := by
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl _ ((simpleRoot Q split i).pow_mem hroot 2)
    rw [←pow_mul]
    exact congrArg Subtype.val (show r^4=1 by rw [←hr,pow_orderOf_eq_one])
  have hc1 := card_le_of_le (show
      simpleRemainder Q split i ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) ≤
        simpleRemainder Q split i ⊓ centralizer ({(r : X ⧸ Q.D)} : Set _) from
    inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hroot)))
  have hc2 := card_le_of_le (show
      simpleRemainder Q split i ⊓ centralizer (omegaOneAmbient (simpleRoot Q split i) : Set (X ⧸ Q.D)) ≤
        simpleRemainder Q split i ⊓ centralizer ({((r^2 : rankOne Q split i) : X ⧸ Q.D)} : Set _) from
    inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr homega)))
  have hv : Nat.card (simpleRemainder Q split i) = 64*Nat.card (simpleRoot Q split j)^4 := by
    simpa only [Nat.mul_zero,Nat.zero_add,Nat.reducePow] using
      suzuki_octagon_radical_card Q split i j 0 μ hB hm hij
  rw [hv] at h1 h2
  constructor <;> nlinarith

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
