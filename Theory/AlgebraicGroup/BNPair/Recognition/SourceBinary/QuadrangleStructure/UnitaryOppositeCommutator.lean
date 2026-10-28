module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.LinearIrreducibility
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryRootDerived
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.ProfileActors
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The opposite unitary-root commutator in a binary quadrangle

Suppose the unitary simple root commuted with its crossed copy. The
three-root factorization would make the radical-derived subgroup the
product of the two root-derived layers. They are disjoint elementary
groups of order at most q, by the actual local unitary marking. The
source reflection swaps them, so the full SL2(q squared) actor acts
nontrivially on this elementary group of order at most q squared.
The checked binary degree bound requires order at least q to the fourth,
a contradiction. Cartan irreducibility then fills the entire intervening
linear root. This proves the first commutator equality in (6A)(c).

The minimum linear actor is SL2(4); q = 2 and q = 4 are included. Every
commutator and action is on the same finite marked quotient. The full
linear actor and faithful unitary local marking remain genuine earlier
inputs, supplied by the original-source application. This argument does
not identify the full unitary actor or construct its radical realization.

Source: Fong--Seitz I (3G), (4B), (5C), (6A)(c), pp.14--16,19--22,26,37.
-/

public noncomputable section
open Theory.GroupTheory Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
private theorem derived_sup_of_commute {G : Type*} [Group G] (A B : Subgroup G)
    (hc : ⁅A,B⁆ = ⊥) : ⁅A ⊔ B,A ⊔ B⁆ = ⁅A,A⁆ ⊔ ⁅B,B⁆ := by
  have hc' (a : A) (b : B) : Commute (A.subtype a) (B.subtype b) :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc a.property) b b.property).symm
  let f := A.subtype.noncommCoprod B.subtype hc'
  have hf : f.range = A ⊔ B := by
    dsimp only [f]
    rw [MonoidHom.noncommCoprod_range,range_subtype,range_subtype]
  apply le_antisymm
  · rw [←hf,←map_commutator_eq]
    rintro x ⟨z,hz,rfl⟩
    have hz' : z ∈ (_root_.commutator A).prod (_root_.commutator B) := by
      rw [_root_.commutator_def,
        show (⊤ : Subgroup (A × B)) = (⊤ : Subgroup A).prod (⊤ : Subgroup B) from (by ext x; simp),
        commutator_prod_prod] at hz
      exact hz
    exact mul_mem_sup
      ((map_subtype_commutator A) ▸ mem_map_of_mem A.subtype hz'.1)
      ((map_subtype_commutator B) ▸ mem_map_of_mem B.subtype hz'.2)
  · exact sup_le (commutator_mono le_sup_left le_sup_left)
      (commutator_mono le_sup_right le_sup_right)

private theorem linear_action_card_lower {F A R : Type*}
    [Field F] [Finite F] [CharP F 2] [Group A] [Group R] [Finite R]
    [IsElementaryAbelian 2 R]
    (μ : A ≃* SL(2,F)) (φ : A →* MulAut R)
    (hnt : ∃ a, φ a ≠ 1) {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) : Nat.card F ^ 2 ≤ Nat.card R := by
  let ρ := (elementaryRepresentation (p := 2) φ).comp μ.symm.toMonoidHom
  have hntρ : ∃ g, ρ g ≠ 1 := by
    obtain ⟨a,ha⟩ := hnt
    refine ⟨μ a,fun he => ha ?_⟩
    ext v
    have hv := congrArg (fun f : Module.End (ZMod 2) (Additive R) => f (Additive.ofMul v)) he
    change Additive.ofMul (φ (μ.symm (μ a)) v) = Additive.ofMul v at hv
    change φ a v = v
    simpa only [MulEquiv.symm_apply_apply] using Additive.ofMul.injective hv
  have hl := Representation.SL2.fixedCodim_top_lower ρ hntρ hn hF
  have hd := fixedCodim_add_finrank ρ ⊤
  have hc : Nat.card R = 2 ^ Module.finrank (ZMod 2) (Additive R) := by
    change Nat.card (Additive R) = _
    simpa only [Nat.card_zmod] using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive R))
  rw [hc,hF,←pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by omega)

open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
theorem remainder_derived_rankOne_normalizes (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    rankOne Q split i ≤ normalizer
      ((⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) := by
  rw [←map_subtype_commutator]
  exact ((rankOne_le_parabolic Q split i).trans (remainder_parabolic_normalizes Q split i hV)).trans
    (normalizer_le_normalizer_characteristic_image _ (_root_.commutator _))

/-- The full actor acts on the intrinsic derived layer, embedded in the same quotient. -/
@[expose] def remainderDerivedAction (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    rankOne Q split i →* MulAut (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) :=
  (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)).normalizerMonoidHom.comp
    (inclusion (remainder_derived_rankOne_normalizes Q split i hV))

@[simp] theorem remainderDerivedAction_apply (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (r : rankOne Q split i)
    (v : (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))) :
    (remainderDerivedAction Q split i hV r v : X ⧸ Q.D) =
      (r : X ⧸ Q.D)*v*(r : X ⧸ Q.D)⁻¹ := rfl

/-- The source reflection moves a nonzero opposite-root derived layer. -/
theorem remainderDerivedAction_nontrivial (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (s : RootReflection Q split i)
    (hne : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ≠ ⊥) :
    ∃ r, remainderDerivedAction Q split i hV r ≠ 1 := by
  by_contra! hh
  apply hne
  apply _root_.eq_bot_iff.mpr
  intro a ha
  have haA := commutator_le_self (simpleRoot Q split j) ha
  have hAV := (opposite_roots_le_remainder Q split j i hij.symm).1
  let v : (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) :=
    ⟨a,commutator_mono hAV hAV ha⟩
  let r : rankOne Q split i := ⟨s.val,s.mem_rankOne⟩
  have he := congrArg (fun f : MulAut (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) =>
    (f v : X ⧸ Q.D)) (hh r⁻¹)
  rw [remainderDerivedAction_apply] at he
  change (s.val : X ⧸ Q.D)⁻¹*a*((s.val : X ⧸ Q.D)⁻¹)⁻¹ = a at he
  rw [inv_inv] at he
  have hac : a ∈ rootAt Q split j (Q.simple i) := by
    rw [rootAt_eq Q split j (Q.simple i) s.val s.class_eq,←he,rightConjugate]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*(s.val : X ⧸ Q.D))*(s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using haA
  exact (disjoint_iff.mp (simpleRoot_disjoint_remainder Q split j)).le
    ⟨haA,cross_root_le_own_remainder Q split hm j i hij.symm hac⟩

/-- If the unitary roots commuted, the radical-derived layer would be the
product of their two small derived layers. -/
theorem remainder_derived_of_cross_commute (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hAi : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    (hc : ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = ⊥) :
    ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ =
      ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ⊔
      rightConjugate ⁅simpleRoot Q split j,simpleRoot Q split j⁆
        (representative (Q.simple i) : X ⧸ Q.D) := by
  have hAC := adjacent_roots_commute Q split hm j i hij.symm hVj hVi
  have hCB := middle_roots_commute Q split hm i j hij hVi hVj
  have hAB : ⁅simpleRoot Q split j ⊔ rootAt Q split i (Q.simple j),
      rootAt Q split j (Q.simple i)⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (sup_le
      (commutator_eq_bot_iff_le_centralizer.mp hc)
      (commutator_eq_bot_iff_le_centralizer.mp hCB))
  have hCC : ⁅rootAt Q split i (Q.simple j),rootAt Q split i (Q.simple j)⁆ = ⊥ := by
    rw [rootAt,rightConjugate,comap_equiv_eq_map_symm',←map_commutator,hAi,Subgroup.map_bot]
  rw [remainder_eq_three_roots Q split hm i j hij,
    derived_sup_of_commute _ _ hAB,derived_sup_of_commute _ _ hAC,hCC,sup_bot_eq]
  congr 1
  simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm',map_commutator]

/-- A full binary linear actor rules out commuting unitary roots by the
minimum representation degree, including the fixed-field order two. -/
theorem cross_root_commutator_nonzero_of_small_derived
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = (2^n)^2)
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split i) (μ : rankOne Q split i ≃* SL(2,K))
    (hAi : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    (he : IsElementaryAbelian 2 (⁅simpleRoot Q split j,simpleRoot Q split j⁆ : Subgroup (X ⧸ Q.D)))
    (hc : Nat.card (⁅simpleRoot Q split j,simpleRoot Q split j⁆ : Subgroup (X ⧸ Q.D)) ≤ 2^n)
    (hne : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ≠ ⊥) :
    ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ ≠ ⊥ := by
  intro hzero
  let A := ⁅simpleRoot Q split j,simpleRoot Q split j⁆
  let B := rightConjugate A (representative (Q.simple i) : X ⧸ Q.D)
  have hB : B ≤ rootAt Q split j (Q.simple i) := comap_mono (commutator_le_self _)
  have hAB : ⁅A,B⁆ = ⊥ := bot_unique ((commutator_mono (commutator_le_self _) hB).trans hzero.le)
  have hdis : Disjoint A B := (simpleRoot_disjoint_remainder Q split j).mono
    (commutator_le_self _) (hB.trans (cross_root_le_own_remainder Q split hm j i hij.symm))
  let := he
  let : IsElementaryAbelian 2 B := by
    rw [show B = rightConjugate A (representative (Q.simple i) : X ⧸ Q.D) from rfl,
      rightConjugate,comap_equiv_eq_map_symm']
    exact IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (A ⊔ B : Subgroup (X ⧸ Q.D)) :=
    IsElementaryAbelian.sup_of_le_centralizer
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hAB))
  have hD := remainder_derived_of_cross_commute Q split hm i j hij hVi hVj hAi hzero
  have hD' : ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ = A ⊔ B := hD
  let : IsElementaryAbelian 2 (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) := hD'.symm ▸ inferInstance
  have hl := linear_action_card_lower μ (remainderDerivedAction Q split i hVi)
    (remainderDerivedAction_nontrivial Q split hm i j hij hVi s hne)
    (show 1 < 2*n by omega) (by rw [hK,←pow_mul]; congr 1; omega)
  have hbound : Nat.card (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) ≤ (2^n)^2 := by
    rw [hD',card_sup_eq_mul_of_normalizes_of_disjoint A B
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hAB)).trans (Subgroup.centralizer_le_normalizer _)) hdis,
      show Nat.card B = Nat.card A from card_rightConjugate _ _]
    exact (Nat.mul_self_le_mul_self hc).trans_eq (pow_two _).symm
  have hh : 2^(4*n) ≤ 2^(2*n) := by
    have := hl.trans hbound
    simp only [hK,←pow_mul] at this
    convert this using 1 <;> congr 1 <;> omega
  have := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hh
  omega
/-- The exact unitary-root commutator, derived from the full original linear
actor and the faithful unitary local group, with neither commutator assumed. -/
theorem unitary_opposite_commutator
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = (2^n)^2)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split i)
    (μ : rankOne Q split i ≃* SL(2,K))
    (ν : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = rootAt Q split i (Q.simple j) := by
  let ξ := (localGroupEquivOfCenterless Q split i hVi μ
    Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans
      Atlas.RankOneFieldAutomorphisms.slEquivPSL
  obtain ⟨he,hc,hne⟩ := simpleRoot_unitary_derived J hn hE hfixed hJ Q split j hVj ν
  exact cross_root_commutator_eq_of_nonzero Q split hm i j hij hVi hVj ξ
    (cross_root_commutator_nonzero_of_small_derived Q split hn hK hm i j hij hVi hVj s μ
      (simpleRoot_commutator_eq_bot_of_linear Q split i ξ) he hc hne)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
