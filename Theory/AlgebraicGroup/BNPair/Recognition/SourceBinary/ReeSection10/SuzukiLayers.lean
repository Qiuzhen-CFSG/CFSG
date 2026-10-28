module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.Input
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiRankOne
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.OctagonRoots
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.Sections
public import Theory.ElementaryAbelian.Quotient

/-!
# The two Suzuki sections in Fong--Seitz II, Section 10

On the same marked quotient, set V = U_s₂ and let A = U₂^(s₁s₂s₁).
The literal (10.2)(iv) and its actual reflection conjugate show that the
whole root-generated R₂ centralizes A. Since R₂ normalizes V and Φ(V),
it normalizes T₂ = Φ(V) A. The commutator equality in (10.3)(i) proves
that T₂ is normal in V. Thus the original conjugation action descends
to V₂ = V/T₂, an elementary two-group, including the parameter m = 0.
The representation is transported through the actual marked Suzuki actor.

The other Suzuki layer is Φ(V)/Z(V). Relation (10.3)(ii) makes Φ(V)
elementary, and (10.3)(iii) places Z(V) in Φ(V) and identifies its exact
ambient image with Ω₁(A). Normality is relative to these numerators.
The full Cartan also normalizes T₂; no field scalar action is assumed.

Source: Fong--Seitz, Groups with a (B,N)-pair of rank 2, II (1974),
printed pp.221--224, the sections preceding (10.4) and (10.11).
The natural four-dimensional identifications, field twists and mixed
coordinate equations remain further reconstruction obligations.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

def perpendicularSuzuki : Subgroup (X ⧸ Q.D) :=
  rootAt Q split 1 (Q.simple 0 * Q.simple 1 * Q.simple 0)

def T2 : Subgroup (X ⧸ Q.D) :=
  phi (simpleRemainder Q split 1) ⊔ perpendicularSuzuki Q split

variable {n m : ℕ} (c : ReeSixHData Q split n m)

include c

theorem perpendicularSuzuki_le_remainder :
    perpendicularSuzuki Q split ≤ simpleRemainder Q split 1 := by
  have hs (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using
      (Q.tits.involutions _ (Q.simple_mem i)).2)
  have hl (b : Bool) (k : ℕ) (hk : k ≤ 8) :
      Q.tits.wordLength (alternatingWord Q b k) = k :=
    wordLength_alternatingWord Q b (by simpa only [c.rotation_eight] using hk)
  have h3 := hl false 3 (by decide)
  have h4 := hl false 4 (by decide)
  have h4' := hl true 4 (by decide)
  have h5 := hl true 5 (by decide)
  simp only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
    Bool.not_false, Bool.not_true, mul_one] at h3 h4 h4' h5
  apply rootAt_le_remainder Q split 1 1
  · simp only [mul_inv_rev, hs, mul_assoc, h3, h4]
  · simp only [mul_inv_rev, hs, mul_assoc, h4', h5]

/-- Relation (10.2)(iv), and its conjugate by the second reflection,
centralize the perpendicular Suzuki root by the entire rank-one group. -/
theorem rankOne_centralizes_perpendicularSuzuki :
    rankOne Q split 1 ≤ centralizer (perpendicularSuzuki Q split : Set (X ⧸ Q.D)) := by
  have h0 : ⁅simpleRoot Q split 1, perpendicularSuzuki Q split⁆ = ⊥ := by
    simpa only [nConj, U, Uat, OneMemClass.coe_one, rightConjugate_one,
      perpendicularSuzuki] using c.relations.ten_two_iv_right 1
  let s := (c.reflections 1).val
  have h1 : ⁅rightConjugate (simpleRoot Q split 1) (s : X ⧸ Q.D),
      perpendicularSuzuki Q split⁆ = ⊥ := by
    have h := c.relations.ten_two_iv_right s
    change ⁅rightConjugate (simpleRoot Q split 1) (s : X ⧸ Q.D),
      rightConjugate (perpendicularSuzuki Q split) (s : X ⧸ Q.D)⁆ = ⊥ at h
    dsimp only [perpendicularSuzuki] at h
    rw [perpendicular_root_stable Q split c.rotation_eight 1 0 (by decide)
      s (c.reflections 1).class_eq] at h
    exact h
  rw [rankOne_eq Q split 1 s (c.reflections 1).class_eq]
  exact sup_le (commutator_eq_bot_iff_le_centralizer.mp h0)
    (commutator_eq_bot_iff_le_centralizer.mp h1)

theorem T2_le_remainder : T2 Q split ≤ simpleRemainder Q split 1 :=
  sup_le (map_subtype_le _) (perpendicularSuzuki_le_remainder Q split c)

theorem remainder_le_T2_normalizer :
    simpleRemainder Q split 1 ≤ normalizer (T2 Q split : Set (X ⧸ Q.D)) := by
  apply le_normalizer_iff_commutator_le_right.mpr
  have h := c.relations.ten_three_frattini 1
  simp only [nConj, OneMemClass.coe_one, rightConjugate_one] at h
  exact (commutator_mono le_rfl (T2_le_remainder Q split c)).trans
    (h.le.trans le_sup_left)

theorem remainder_le_kernel : simpleRemainder Q split 1 ≤ localKernel Q 1 :=
  remainder_le_panelKernel_of_marking Q split 1 c.suzuki (matrixRootSylow m)
    (c.suzukiBorel.trans (by
      change normalizer (BenderSuzuki.MatrixGroups.SuzukiRootSubgroup m :
        Set (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) =
        normalizer ((matrixRootSylow m : Subgroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
          Set (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
      rw [matrixRootSylow_carrier]))
    (suzuki_normalizer_index m (matrixRootSylow m))

theorem rankOne_normalizes_T2 :
    rankOne Q split 1 ≤ normalizer (T2 Q split : Set (X ⧸ Q.D)) := by
  have hV := (rankOne_le_parabolic Q split 1).trans
    (remainder_parabolic_normalizes Q split 1 (remainder_le_kernel Q split c))
  exact (le_inf
    (hV.trans (normalizer_le_normalizer_characteristic_image _ (frattini _)))
    ((rankOne_centralizes_perpendicularSuzuki Q split c).trans
      (Subgroup.centralizer_le_normalizer _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem T2_product : (T2 Q split : Set (X ⧸ Q.D)) =
    (phi (simpleRemainder Q split 1) : Set (X ⧸ Q.D)) *
      (perpendicularSuzuki Q split : Set (X ⧸ Q.D)) := by
  exact coe_mul_of_right_le_normalizer_left _ _
    ((perpendicularSuzuki_le_remainder Q split c).trans
      ((simpleRemainder Q split 1).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (frattini _))))

/-- The definition agrees with the exact derived-subgroup product on p.221. -/
theorem T2_derived_product : (T2 Q split : Set (X ⧸ Q.D)) =
    ((⁅simpleRemainder Q split 1, simpleRemainder Q split 1⁆ : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) *
      (perpendicularSuzuki Q split : Set (X ⧸ Q.D)) := by
  have h := c.relations.ten_three_frattini 1
  simp only [nConj, OneMemClass.coe_one, rightConjugate_one] at h
  rw [h]
  exact T2_product Q split c

def V2Section : RootSection Q split 1 where
  numerator := simpleRemainder Q split 1
  le_radical := le_rfl
  normalized := (rankOne_le_parabolic Q split 1).trans
    (remainder_parabolic_normalizes Q split 1 (remainder_le_kernel Q split c))
  denominator := (T2 Q split).subgroupOf (simpleRemainder Q split 1)
  normal := normal_subgroupOf_of_le_normalizer (remainder_le_T2_normalizer Q split c)
  invariant r := by
    let hR := (rankOne_le_parabolic Q split 1).trans
      (remainder_parabolic_normalizes Q split 1 (remainder_le_kernel Q split c))
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      exact (mem_normalizer_iff.mp (rankOne_normalizes_T2 Q split c r.property) _).mp hy
    · intro x hx
      refine ⟨(simpleRemainder Q split 1).normalizerMonoidHom
        ⟨(r⁻¹ : rankOne Q split 1), hR (inv_mem r.property)⟩ x, ?_, ?_⟩
      · exact (mem_normalizer_iff.mp
          (rankOne_normalizes_T2 Q split c (inv_mem r.property)) _).mp hx
      · change ((simpleRemainder Q split 1).normalizerMonoidHom.comp (inclusion hR)) r
          (((simpleRemainder Q split 1).normalizerMonoidHom.comp (inclusion hR)) r⁻¹ x) = x
        rw [map_inv]
        exact MulEquiv.apply_symm_apply _ x

theorem V2Section_effectiveDenominator :
    (V2Section Q split c).effectiveDenominator = (V2Section Q split c).denominator := by
  rw [RootSection.effectiveDenominator_eq, sup_eq_right]
  intro x hx
  change (x : X ⧸ Q.D) ∈ phi (simpleRemainder Q split 1) ⊔ perpendicularSuzuki Q split
  exact (show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left)
    (mem_map_of_mem (simpleRemainder Q split 1).subtype hx)

instance V2Section_elementary : IsElementaryAbelian 2 (V2Section Q split c).Carrier := by
  let e := QuotientGroup.quotientMulEquivOfEq (V2Section_effectiveDenominator Q split c)
  exact IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective

/-- Conjugation on the actual quotient is a binary representation. -/
def V2Representation : Representation (ZMod 2) (rankOne Q split 1)
    (Additive (V2Section Q split c).Carrier) where
  toFun r := ((V2Section Q split c).action r).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by ext x; simp only [map_one]; rfl
  map_mul' r s := by ext x; simp only [map_mul]; rfl

@[simp] theorem V2Representation_mk (r : rankOne Q split 1)
    (x : simpleRemainder Q split 1) :
    V2Representation Q split c r (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk ((V2Section Q split c).numeratorAction r x)) := rfl

/-- The actor is the marked full Suzuki group, including Sz(2). -/
def suzukiV2Representation : Representation (ZMod 2)
    (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) (Additive (V2Section Q split c).Carrier) :=
  (V2Representation Q split c).comp
    (suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel).symm.toMonoidHom

@[simp] theorem suzukiV2Representation_source (r : rankOne Q split 1)
    (x : simpleRemainder Q split 1) :
    suzukiV2Representation Q split c (suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel r)
      (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk ((V2Section Q split c).numeratorAction r x)) := by
  change V2Representation Q split c
    ((suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel).symm
      (suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel r)) _ = _
  rw [MulEquiv.symm_apply_apply, V2Representation_mk]

/-- The full source Cartan normalizes the denominator, without a torus table. -/
theorem cartan_normalizes_T2 :
    Q.tits.B ⊓ Q.tits.N ≤ normalizer (T2 Q split : Set (X ⧸ Q.D)) := by
  have hV : Q.tits.B ⊓ Q.tits.N ≤ normalizer (simpleRemainder Q split 1 : Set (X ⧸ Q.D)) :=
    inf_le_left.trans ((Q.tits.B_le_standardParabolic {Q.simple 1}).trans
    (remainder_parabolic_normalizes Q split 1 (remainder_le_kernel Q split c)))
  exact (le_inf
    (hV.trans (normalizer_le_normalizer_characteristic_image _ (frattini _)))
    (rootAt_torus_normalizes Q split 1 _)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The second Frattini equality in (10.3) makes Φ(Uₛ₂) elementary. -/
theorem phiRemainder_elementary : IsElementaryAbelian 2 (phi (simpleRemainder Q split 1)) := by
  let A := phi (simpleRemainder Q split 1)
  let : Fact (IsPGroup 2 A) :=
    ⟨split.isTwo.to_le ((map_subtype_le _).trans inf_le_left)⟩
  apply (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
  apply (Subgroup.map_injective A.subtype_injective)
  rw [Subgroup.map_bot]
  change phi (phi (simpleRemainder Q split 1)) = ⊥
  have h := c.relations.ten_three_frattini_square 1
  simpa only [nConj, OneMemClass.coe_one, rightConjugate_one] using h

theorem phiRemainder_commutator :
    ⁅phi (simpleRemainder Q split 1), simpleRemainder Q split 1⁆ =
      zeta (simpleRemainder Q split 1) := by
  have h := (c.relations.ten_three_center 1).trans
    (c.relations.ten_three_center_remainder 1)
  simpa only [nConj, OneMemClass.coe_one, rightConjugate_one] using h

theorem centerRemainder_le_phi :
    zeta (simpleRemainder Q split 1) ≤ phi (simpleRemainder Q split 1) := by
  rw [← phiRemainder_commutator Q split c]
  exact le_normalizer_iff_commutator_le_left.mp
    ((simpleRemainder Q split 1).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (frattini _)))

/-- The four-dimensional layer sought in (10.11), before natural-module identification. -/
def phiCenterSection : RootSection Q split 1 where
  numerator := phi (simpleRemainder Q split 1)
  le_radical := map_subtype_le _
  normalized := ((rankOne_le_parabolic Q split 1).trans
    (remainder_parabolic_normalizes Q split 1 (remainder_le_kernel Q split c))).trans
      (normalizer_le_normalizer_characteristic_image _ (frattini _))
  denominator := (zeta (simpleRemainder Q split 1)).subgroupOf (phi (simpleRemainder Q split 1))
  normal := normal_subgroupOf_of_le_normalizer
    ((map_subtype_le _).trans ((simpleRemainder Q split 1).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (center _))))
  invariant r := by
    have hR := ((rankOne_le_parabolic Q split 1).trans
      (remainder_parabolic_normalizes Q split 1 (remainder_le_kernel Q split c))).trans
        (normalizer_le_normalizer_characteristic_image _ (frattini _))
    have hZ := ((rankOne_le_parabolic Q split 1).trans
      (remainder_parabolic_normalizes Q split 1 (remainder_le_kernel Q split c))).trans
        (normalizer_le_normalizer_characteristic_image _ (center _))
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      exact (mem_normalizer_iff.mp (hZ r.property) _).mp hy
    · intro x hx
      refine ⟨(phi (simpleRemainder Q split 1)).normalizerMonoidHom
        ⟨(r⁻¹ : rankOne Q split 1), hR (inv_mem r.property)⟩ x, ?_, ?_⟩
      · exact (mem_normalizer_iff.mp (hZ (inv_mem r.property)) _).mp hx
      · change ((phi (simpleRemainder Q split 1)).normalizerMonoidHom.comp (inclusion hR)) r
          (((phi (simpleRemainder Q split 1)).normalizerMonoidHom.comp (inclusion hR)) r⁻¹ x) = x
        rw [map_inv]
        exact MulEquiv.apply_symm_apply _ x

instance phiCenterSection_elementary : IsElementaryAbelian 2 (phiCenterSection Q split c).Carrier := by
  let : IsElementaryAbelian 2 (phiCenterSection Q split c).numerator :=
    phiRemainder_elementary Q split c
  exact IsElementaryAbelian.quotient (phiCenterSection Q split c).denominator

theorem phiCenterSection_denominator_image :
    (phiCenterSection Q split c).denominator.map (phiCenterSection Q split c).numerator.subtype =
      omega (perpendicularSuzuki Q split) := by
  change ((zeta (simpleRemainder Q split 1)).subgroupOf
    (phi (simpleRemainder Q split 1))).map (phi (simpleRemainder Q split 1)).subtype = _
  rw [map_subgroupOf_eq_of_le (centerRemainder_le_phi Q split c)]
  symm
  simpa only [nConj, OneMemClass.coe_one, rightConjugate_one, Uat, perpendicularSuzuki] using
    c.relations.ten_three_center_remainder 1

end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
