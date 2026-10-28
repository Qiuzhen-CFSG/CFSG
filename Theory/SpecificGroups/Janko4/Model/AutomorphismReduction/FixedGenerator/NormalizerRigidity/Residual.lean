module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer
public import Theory.GroupTheory.CharacteristicRestrictionInnerSquares

/-!
# Central characters of the actual J₄ involution centralizer

Let C be the literal matrix centralizer and Q = O₂(C). The certified seed
normal closure is a normal two-subgroup of C, and its relative centralizer
consists of 1 and a. Thus an automorphism fixing Q pointwise displaces each
c by a central element of ⟨a⟩. This displacement is a homomorphism vanishing
on Q, so descends to the actual quotient C/Q.

The seed (XYXYY)^11 belongs to Q. Its two X occurrences and odd Y exponent
force the character to vanish on Y. Generation by X,Y then leaves precisely
the identity action or the possible central twist X ↦ aX, Y ↦ Y. Exclusion of
an ambient matrix realization of that twist is a separate linear calculation.

Source motivation: GLS3 Table 5.3i and Aschbacher–Smith, printed p.1172,
16.1.5(9). The actual ATLAS words and embeddings are certified in
`NormalizerSquares.LocalAction.TwoCoreCentralizer`; no source table is assumed.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerRigidity
open NormalizerSquares NormalizerSquares.TwoCoreCentralizerData

/-- The seed normal closure, transported to the full literal centralizer. -/
private def seedInclusion : localSubgroup ≃* involutionCentralizer :=
  (MulEquiv.subgroupCongr localSubgroup_eq_top).trans Subgroup.topEquiv

private theorem seedNormalClosure_le_twoCore :
    localNormalClosure.map seedInclusion.toMonoidHom ≤ involutionTwoCore :=
  le_sSup ⟨localNormalClosure_normal.map _ seedInclusion.surjective,
    localNormalClosure_isPGroup.map _⟩

theorem seed_mem_twoCore :
    (localX * localY * localX * localY * localY) ^ 11 ∈ involutionTwoCore :=
  seedNormalClosure_le_twoCore (Subgroup.mem_map.mpr
    ⟨localSeed, localSeed_mem_normalClosure, rfl⟩)

/-- The relative centralizer of Q is exactly the two possible central scalars. -/
theorem twoCore_centralizer_cases (z : involutionCentralizer)
    (hz : z ∈ Subgroup.centralizer (involutionTwoCore : Set involutionCentralizer)) :
    z = 1 ∨ z = centralInvolution := by
  have he : seedInclusion.symm z ∈ Subgroup.centralizer
      (localNormalClosure : Set localSubgroup) := by
    intro n hn
    apply seedInclusion.injective
    simpa only [map_mul, seedInclusion.apply_symm_apply] using
      (Subgroup.centralizer_le seedNormalClosure_le_twoCore hz)
        (seedInclusion n) (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
  rcases TwoCoreComparison.localSeedCentralizer_cases (seedInclusion.symm z) he with he | he
  · left
    simpa only [seedInclusion.apply_symm_apply, map_one] using congrArg seedInclusion he
  · right
    have ha : seedInclusion subgroupInvolution = centralInvolution := rfl
    simpa only [seedInclusion.apply_symm_apply, ha] using congrArg seedInclusion he

variable (β : MulAut involutionCentralizer)
    (hβ : MulAut.characteristic involutionTwoCore β = 1)

include hβ

theorem fixes_twoCore (q : involutionCentralizer) (hq : q ∈ involutionTwoCore) : β q = q :=
  congrArg Subtype.val (DFunLike.congr_fun hβ (⟨q, hq⟩ : involutionTwoCore))

/-- The displacement belongs to the actual relative central kernel. -/
theorem displacement_mem_centralizer (x : involutionCentralizer) :
    x⁻¹ * β x ∈ Subgroup.centralizer (involutionTwoCore : Set involutionCentralizer) := by
  intro n hn
  have he := fixes_twoCore β hβ (x * n * x⁻¹)
    ((inferInstance : involutionTwoCore.Normal).conj_mem n hn x)
  simp only [map_mul, map_inv, fixes_twoCore β hβ n hn] at he
  have hh := congrArg (fun t : involutionCentralizer => x⁻¹ * t * β x) he
  group at hh
  simpa only [mul_assoc, zpow_neg_one] using hh.symm

/-- Pointwise fixation of Q permits only a central-involution displacement. -/
theorem displacement_cases (x : involutionCentralizer) :
    x⁻¹ * β x = 1 ∨ x⁻¹ * β x = centralInvolution :=
  twoCore_centralizer_cases _ (displacement_mem_centralizer β hβ x)

private theorem displacement_mem_zpowers (x : involutionCentralizer) :
    x⁻¹ * β x ∈ Subgroup.zpowers centralInvolution := by
  rcases displacement_cases β hβ x with h | h
  · rw [h]; exact (Subgroup.zpowers _).one_mem
  · rw [h]; exact Subgroup.mem_zpowers _

/-- The displacement is a homomorphism into the literal central subgroup. -/
def residualDisplacement : involutionCentralizer →* Subgroup.zpowers centralInvolution where
  toFun x := ⟨x⁻¹ * β x, by exact displacement_mem_zpowers β hβ x⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change (x * y)⁻¹ * β (x * y) = (x⁻¹ * β x) * (y⁻¹ * β y)
    have hc := (Subgroup.mem_center_iff.mp
      ((Subgroup.zpowers_le.mpr centralInvolution_mem_center)
        (displacement_mem_zpowers β hβ x))) y⁻¹
    simp only [map_mul, mul_inv_rev]
    calc
      y⁻¹ * x⁻¹ * (β x * β y) = (y⁻¹ * (x⁻¹ * β x)) * β y := by group
      _ = ((x⁻¹ * β x) * y⁻¹) * β y := by rw [hc]
      _ = (x⁻¹ * β x) * (y⁻¹ * β y) := mul_assoc _ _ _

/-- The displacement vanishes on Q itself. -/
theorem twoCore_le_residualDisplacement_ker :
    involutionTwoCore ≤ (residualDisplacement β hβ).ker := by
  intro q hq
  apply Subtype.ext
  change q⁻¹ * β q = 1
  rw [fixes_twoCore β hβ q hq, inv_mul_cancel]

/-- The remaining action is a character of the actual quotient C/Q. -/
def residualCharacter : involutionCentralizer ⧸ involutionTwoCore →*
    Subgroup.zpowers centralInvolution :=
  QuotientGroup.lift _ (residualDisplacement β hβ) (twoCore_le_residualDisplacement_ker β hβ)

theorem residualCharacter_spec (x : involutionCentralizer) :
    β x = x * (residualCharacter β hβ (QuotientGroup.mk x) : involutionCentralizer) := by
  change β x = x * (x⁻¹ * β x)
  rw [mul_inv_cancel_left]

private theorem residualDisplacement_pow_two (x : involutionCentralizer) :
    residualDisplacement β hβ x ^ 2 = 1 := by
  apply Subtype.ext
  change (x⁻¹ * β x) ^ 2 = 1
  exact localTwoCoreCentralizerControl.2 _ (displacement_mem_centralizer β hβ x)

/-- The odd exponent in the concrete seed relation kills the Y-displacement. -/
theorem fixes_localY : β localY = localY := by
  let d := residualDisplacement β hβ
  have hx : d localX ^ 2 = 1 := residualDisplacement_pow_two β hβ _
  have hy : d localY ^ 2 = 1 := residualDisplacement_pow_two β hβ _
  have hs : d ((localX * localY * localX * localY * localY) ^ 11) = 1 :=
    twoCore_le_residualDisplacement_ker β hβ seed_mem_twoCore
  simp only [map_pow, map_mul] at hs
  have he : d localX * d localY * d localX * d localY * d localY = d localY := by
    calc
      _ = (d localX ^ 2) * (d localY ^ 2) * d localY := by
        rw [pow_two, pow_two]
        rw [mul_assoc (d localX) (d localY) (d localX), mul_comm' (d localY) (d localX)]
        simp only [← mul_assoc]
      _ = d localY := by rw [hx, hy, one_mul, one_mul]
  rw [he] at hs
  have hp : d localY ^ 11 = d localY := by
    calc
      _ = (d localY ^ 2) ^ 5 * d localY := by rw [← pow_mul, ← pow_succ]
      _ = d localY := by rw [hy, one_pow, one_mul]
  rw [hp] at hs
  have hv := congrArg (fun z : Subgroup.zpowers centralInvolution =>
    (z : involutionCentralizer)) hs
  change localY⁻¹ * β localY = 1 at hv
  exact (inv_mul_eq_one.mp hv).symm

theorem localX_cases : β localX = localX ∨ β localX = centralInvolution * localX := by
  rcases displacement_cases β hβ localX with hx | hx
  · exact Or.inl (inv_mul_eq_one.mp hx).symm
  · right
    have he : β localX = localX * centralInvolution := by
      rw [← hx, mul_inv_cancel_left]
    exact he.trans ((Subgroup.mem_center_iff.mp centralInvolution_mem_center) localX)

/-- Generation upgrades the untwisted branch to the identity automorphism. -/
theorem eq_one_of_fixes_localX (hx : β localX = localX) : β = 1 := by
  apply MulEquiv.ext
  intro x
  change β x = x
  have hxmem : x ∈ Subgroup.closure ({localX, localY} : Set involutionCentralizer) := by
    rw [show Subgroup.closure ({localX, localY} : Set involutionCentralizer) = ⊤
      from localSubgroup_eq_top]
    trivial
  refine Subgroup.closure_induction (fun z hz => ?_) ?_ (fun z w _ _ hz hw => ?_)
    (fun z _ hz => ?_) hxmem
  · rcases hz with rfl | hz
    · exact hx
    · rw [Set.mem_singleton_iff] at hz
      subst z
      exact fixes_localY β hβ
  · exact map_one β
  · exact (map_mul β z w).trans (congrArg₂ (· * ·) hz hw)
  · exact (map_inv β z).trans (congrArg Inv.inv hz)

end Janko4.OuterReduction.FixedGenerator.NormalizerRigidity
