module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.BorelWeylPinning
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The binary source Cartan, Borel, braid and torus equations

At q=2 every one of the six actual source root subgroups has order two.
The full H normalizes each root, so the elementary order-two normalizer
lemma makes it centralize every root and hence U. It follows that H is
normalized by B = UH; it is already normalized by N. Thus H is normal in
the full group. Core-freeness of the original Borel forces H = 1.

This discharges the Cartan commutativity premise of BorelWeylPinning at
q=2. The constructed Borel equals the actual B = U, and (rs)^6 = 1 because
its Weyl image is one and the Weyl kernel H is trivial. Every torus equation
also follows, since the only field unit is one. All maps remain in the
same quotient and the source reflections retain both endpoint placements.

These are genuine binary source equations without perfectness, Thomas
recognition, or substitution of the proper derived subgroup for G₂(2).
The binary mixed positive equations and the two orthogonal-root fixed-point
equations still remain to be proved. The literal consumer is
FongSeitzBinary/GTwoSource/CartanApplication.

Source: Fong--Seitz II (9A), printed pp.211,214--215, for the full binary
case and its separate treatment; §7 for H and the rank-one pinnings.
The proof here uses only the existing split geometry, source root
coordinates and the actual core-free Borel hypothesis.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)

theorem positiveCarrier_torus_normalizes (short : Fin 2) (k : Fin 6) :
    Q.tits.B ⊓ Q.tits.N ≤ normalizer (positiveCarrier Q split short k : Set _) := by
  fin_cases k
  · exact rootAt_torus_normalizes Q split _ _
  · exact rootAt_torus_normalizes Q split _ _
  · exact rootAt_torus_normalizes Q split _ _
  · exact rootAt_torus_normalizes Q split _ _
  · exact torus_normalizes_simpleRoot Q split _
  · exact torus_normalizes_simpleRoot Q split _

variable (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)

include hK μ n short in
theorem positiveCarrier_card (k : Fin 6) :
    Nat.card (positiveCarrier Q split short k) = Nat.card F := by
  rw [← alignedSourceRoots_range Q split hK μ n short k]
  exact (Nat.card_congr (MonoidHom.ofInjective
    (alignedSourceRoots_injective Q split hK μ n short k)).toEquiv).symm.trans
      (Nat.card_congr Multiplicative.toAdd)

include hK μ n short in
theorem binary_cartan_centralizes_unipotent (hm : rotationOrder Q = 6) (hF : Nat.card F = 2) :
    Q.tits.B ⊓ Q.tits.N ≤ centralizer (split.U : Set (X ⧸ Q.D)) := by
  apply le_centralizer_iff.mpr
  rw [← alignedSourceRoots_generated Q split hK μ n short hm]
  apply (closure_le _).mpr
  rintro x ⟨⟨k,a⟩,rfl⟩
  have hc : Q.tits.B ⊓ Q.tits.N ≤ centralizer (positiveCarrier Q split short k : Set _) :=
    (positiveCarrier_torus_normalizes Q split short k).trans
      (normalizer_le_centralizer_of_card_two _
        ((positiveCarrier_card Q split hK μ n short k).trans hF))
  apply (le_centralizer_iff.mp hc)
  rw [← alignedSourceRoots_range Q split hK μ n short k]
  exact ⟨.ofAdd a,rfl⟩

include hK μ n short in
/-- The full source Cartan is trivial over F₂, using core-freeness and no module classification. -/
theorem binary_cartan_eq_bot (hm : rotationOrder Q = 6) (hF : Nat.card F = 2)
    (hcore : Q.tits.B.normalCore = ⊥) : Q.tits.B ⊓ Q.tits.N = ⊥ := by
  let H := Q.tits.B ⊓ Q.tits.N
  have hc : split.U ≤ centralizer (H : Set (X ⧸ Q.D)) :=
    le_centralizer_iff.mp (binary_cartan_centralizes_unipotent Q split hK μ n short hm hF)
  have hB : Q.tits.B ≤ normalizer (H : Set (X ⧸ Q.D)) := by
    rw [← split.factorization]
    exact sup_le (hc.trans (Subgroup.centralizer_le_normalizer _)) H.le_normalizer
  have hN : Q.tits.N ≤ normalizer (H : Set (X ⧸ Q.D)) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_right).mp Q.tits.intersection_normal
  have hn : normalizer (H : Set (X ⧸ Q.D)) = ⊤ := by
    apply top_unique
    rw [← Q.tits.generate]
    exact (closure_le _).mpr (Set.union_subset hB hN)
  let : H.Normal := normalizer_eq_top_iff.mp hn
  exact le_bot_iff.mp (hcore ▸ (normal_le_normalCore.mpr (show H ≤ Q.tits.B from inf_le_left)))

include split hK μ n short in
/-- Discharge the Cartan commutativity input of the actual binary Borel--Weyl maps. -/
theorem binaryCartanCommutative (hm : rotationOrder Q = 6) (hF : Nat.card F = 2)
    (hcore : Q.tits.B.normalCore = ⊥) : IsMulCommutative ↥(Q.tits.B ⊓ Q.tits.N) := by
  rw [binary_cartan_eq_bot Q split hK μ n short hm hF hcore]
  infer_instance

/-- The binary datum uses the SAME six roots and source reflections. -/
def binarySourceBorelWeyl (hm : rotationOrder Q = 6) (hF : Nat.card F = 2)
    (hcore : Q.tits.B.normalCore = ⊥) : BorelWeylData F (X ⧸ Q.D) :=
  sourceBorelWeyl Q split hK μ n short (binaryCartanCommutative Q split hK μ n short hm hF hcore)

/-- Even the braid follows in the binary case: its Weyl class is one and H is trivial. -/
theorem binarySourceBorelWeyl_braid (hm : rotationOrder Q = 6) (hF : Nat.card F = 2)
    (hcore : Q.tits.B.normalCore = ⊥) :
    ((binarySourceBorelWeyl Q split hK μ n short hm hF hcore).r *
      (binarySourceBorelWeyl Q split hK μ n short hm hF hcore).s)^6 = 1 := by
  let z : Q.tits.N := ((n (1-short)).val*(n short).val)^6
  have hz : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) z = 1 := by
    simp only [z,map_pow,map_mul,(n (1-short)).class_eq,(n short).class_eq]
    have he : orderOf (Q.simple (1-short)*Q.simple short) = 6 := by
      fin_cases short
      · simpa [rotationOrder] using (SemiconjBy.orderOf_eq (Q.simple 0) (show
          SemiconjBy (Q.simple 0) (Q.simple 1*Q.simple 0) (Q.simple 0*Q.simple 1) from
            (mul_assoc _ _ _).symm)).trans hm
      · exact hm
    rw [← he]
    exact pow_orderOf_eq_one _
  have hmem : (z : X ⧸ Q.D) ∈ Q.tits.B ⊓ Q.tits.N := (QuotientGroup.eq_one_iff z).mp hz
  rw [binary_cartan_eq_bot Q split hK μ n short hm hF hcore,mem_bot] at hmem
  exact hmem


/-- In the binary datum the actual full torus is trivial. -/
theorem binarySourceBorelWeyl_torus (hm : rotationOrder Q = 6) (hF : Nat.card F = 2)
    (hcore : Q.tits.B.normalCore = ⊥) (p : Fˣ × Fˣ) :
    (binarySourceBorelWeyl Q split hK μ n short hm hF hcore).torus p = 1 := by
  have hh := alignedPairTorus_mem Q split hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore) p
  rw [binary_cartan_eq_bot Q split hK μ n short hm hF hcore,mem_bot] at hh
  exact hh

omit [Finite F] [CharP F 2] in
private theorem binary_unit_eq_one (hF : Nat.card F = 2) (a : Fˣ) : a = 1 := by
  obtain ⟨x,hx,hu⟩ := (Nat.card_eq_two_iff' (0 : F)).mp hF
  exact Units.ext ((hu a a.ne_zero).trans (hu 1 one_ne_zero).symm)

/-- The binary torus weights hold on all six actual source root maps. -/
theorem binarySourceBorelWeyl_torus_root (hm : rotationOrder Q = 6) (hF : Nat.card F = 2)
    (hcore : Q.tits.B.normalCore = ⊥) (l m : Fˣ) (i : Fin 6) (a : F) :
    let d := binarySourceBorelWeyl Q split hK μ n short hm hF hcore
    d.torus (l,m) * d.x i a * (d.torus (l,m))⁻¹ = d.x i (BorelWeylData.weight l m i * a) := by
  obtain rfl := binary_unit_eq_one hF l
  obtain rfl := binary_unit_eq_one hF m
  dsimp only
  rw [binarySourceBorelWeyl_torus]
  fin_cases i <;> simp [BorelWeylData.weight]

theorem binarySourceBorelWeyl_r_torus (hm : rotationOrder Q = 6) (hF : Nat.card F = 2)
    (hcore : Q.tits.B.normalCore = ⊥) (l m : Fˣ) :
    let d := binarySourceBorelWeyl Q split hK μ n short hm hF hcore
    d.r * d.torus (l,m) * d.r⁻¹ = d.torus (l,l/m) := by
  dsimp only
  simp only [binarySourceBorelWeyl_torus,mul_one,mul_inv_cancel]

theorem binarySourceBorelWeyl_s_torus (hm : rotationOrder Q = 6) (hF : Nat.card F = 2)
    (hcore : Q.tits.B.normalCore = ⊥) (l m : Fˣ) :
    let d := binarySourceBorelWeyl Q split hK μ n short hm hF hcore
    d.s * d.torus (l,m) * d.s⁻¹ = d.torus (m,l) := by
  dsimp only
  simp only [binarySourceBorelWeyl_torus,mul_one,mul_inv_cancel]

/-- The constructed binary Borel is the full original B. -/
theorem binarySourceBorelWeyl_borel (hm : rotationOrder Q = 6) (hF : Nat.card F = 2)
    (hcore : Q.tits.B.normalCore = ⊥) :
    (binarySourceBorelWeyl Q split hK μ n short hm hF hcore).borel = Q.tits.B := by
  have ht : (binarySourceBorelWeyl Q split hK μ n short hm hF hcore).torus.range = ⊥ := by
    apply le_bot_iff.mp
    rintro x ⟨p,rfl⟩
    exact mem_bot.mpr (binarySourceBorelWeyl_torus Q split hK μ n short hm hF hcore p)
  rw [BorelWeylData.borel, ht, sup_bot_eq]
  change (alignedSourceRoots Q split hK μ n short).generated = _
  rw [alignedSourceRoots_generated Q split hK μ n short hm]
  have he := split.factorization
  rw [binary_cartan_eq_bot Q split hK μ n short hm hF hcore, sup_bot_eq] at he
  exact he

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
