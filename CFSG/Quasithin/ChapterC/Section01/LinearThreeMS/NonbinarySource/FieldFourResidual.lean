module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.FieldFourCharacteristic
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.SolvableResidual.NormalSupplement

/-!
# The original nonbinary F4 component is the actual residual

For the field-four test of the exact C.1.31 hypotheses, keep the same
root-generated matrix parabolic and the candidate A join [U,A] from
`FieldFourCharacteristic`. A nontrivial coroot scalar expresses every
signed long-simple root element, at every field parameter, as a
commutator in A. Thus A is perfect. Direct conjugation proves that
A join [U,A] is normal in U join A; its quotient is a two-group. The
solvable residual contains A and [U,A], and the solvable quotient gives
the reverse inclusion. The same candidate is therefore perfect and is
also the two-residual.

The final field-four application supplies these statements together with
the already proved MS3 on the literal original matrix subgroups. This
identifies the candidate intrinsically but does not identify its two-core
quotient with SL₃(4), establish that it is a C-component, or certify the
fitting, SQTK, Sylow and odd-index radical clauses. No full nonbinary
counterexample or C.1.34 classification is asserted.

The coroot-word proof adapts `F4ChevalleyCorootWords` and
`ReeF4.ParabolicAmalgam.Geometry.CorootRealization` to the original finite
coefficient field, including even degree. Source: Steinberg, *Lectures on
Chevalley Groups*, Theorem 1 and Lemmas 5–6; GLS3 §1.12 and §2.6;
Aschbacher–Smith C.1.31–34, printed pp.135–137, and the original F4
examples of Meierfrankenfeld–Stellmacher (1993), printed p.831.
-/

public noncomputable section
open Subgroup Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Classical Matrix commutatorElement
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.F4Original
variable {F : Type} [Field F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def rankOneWord (r : F4Chevalley.Root) (t : F) : Ambient F :=
  root r t * root (-r) (-t⁻¹) * root r t

private def corootWord (r : F4Chevalley.Root) (t : F) : Ambient F :=
  rankOneWord r t * rankOneWord r (-1)

private abbrev rankOneWordMatrix (r : F4Chevalley.Root) (t : F) :=
  (rankOneWord r t).val

private abbrev corootWordMatrix (r : F4Chevalley.Root) (t : F) :=
  (corootWord r t).val

private abbrev diag (i : typeF4RootPairing_base.support) (u : Fˣ) :=
  integralChevalleyTorusElement (P := typeF4RootPairing)
    (integralChevalleySimpleCorootParameter i u)

private theorem diag_tits (i : typeF4RootPairing_base.support) (u : Fˣ) :
    rootCurveTitsWord (S := F) [i] * diag i u =
      (diag i u)⁻¹ * rootCurveTitsWord (S := F)
        [i] := by
  apply Units.ext
  change specializeMatrix (titsWord [i]) * Matrix.diagonal _ =
    Matrix.diagonal _ * specializeMatrix (titsWord [i])
  simp only [titsWord, Matrix.mul_one]
  ext row col
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : titsLift i row col = 0
  · simp [specializeMatrix, hz]
  · have hw := titsLift_respectsChevalleyGrading i
      row col hz (i : F4Chevalley.Root)
    have hn : chevalleyBasisWeight (P := typeF4RootPairing) row (i : F4Chevalley.Root) =
        -chevalleyBasisWeight (P := typeF4RootPairing) col (i : F4Chevalley.Root) := by
      rw [hw]
      cases col with
      | inl j => simp [chevalleyBasisWeight]
      | inr j =>
        exact typeF4RootPairing.pairingIn_reflectionPerm_self_right ℤ j _
    have heval (a : F4Chevalley.BasisIndex) :
        chevalleyBasisTorusUnit (P := typeF4RootPairing)
          (integralChevalleySimpleCorootParameter i u) a =
        u ^ (-chevalleyBasisWeight (P := typeF4RootPairing) a (i : F4Chevalley.Root)) := by
      unfold chevalleyBasisTorusUnit integralChevalleySimpleCorootParameter
      rw [Finset.prod_eq_single i]
      · simp only [if_true]
      · intro j _ hj
        simp [hj]
      · simp
    have hu : chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter i u) col =
        (chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter i u) row)⁻¹ := by
      rw [heval, heval, hn]
      simp

    rw [hu]
    exact mul_comm _ _

private theorem diag_root (i : typeF4RootPairing_base.support) (u : Fˣ)
    (r : F4Chevalley.Root) (t : F) :
    (diag i u)⁻¹ * F4Chevalley.rootCurve r t * diag i u =
      F4Chevalley.rootCurve r
        (((u ^ typeF4RootPairing.pairingIn ℤ r (i : F4Chevalley.Root) :
          Fˣ) : F) * t) := by
  exact integralChevalleyRootCurve_simpleCoroot_conjugation
    i u r t

private theorem diag_mul (i : typeF4RootPairing_base.support) (u v : Fˣ) :
    diag i (u * v) = diag i u * diag i v := by
  rw [diag, ← integralChevalleyTorusElement_mul]
  congr 1
  funext j
  simp only [integralChevalleySimpleCorootParameter, Pi.mul_apply]
  split_ifs <;> simp

private theorem rankOneWordMatrix_one (i : typeF4RootPairing_base.support) :
    (rankOneWordMatrix (F := F) (i : F4Chevalley.Root) 1) =
      rootCurveTitsWord (S := F) [i] := by
  rw [rootCurveTitsWord_cons, rootCurveTitsWord_nil, mul_one]
  change F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
    F4Chevalley.rootCurve _ 1 = _
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    rootCurveUnit_simple, rootCurveUnit_neg_simple,
    inv_one]

private theorem rankOneWordMatrix_neg_one (i : typeF4RootPairing_base.support) :
    rankOneWordMatrix (F := F) (i : F4Chevalley.Root) (-1) =
      (rankOneWordMatrix (F := F) (i : F4Chevalley.Root) 1)⁻¹ := by
  change F4Chevalley.rootCurve _ (-1) * F4Chevalley.rootCurve _ (-(-1)⁻¹) *
      F4Chevalley.rootCurve _ (-1) =
    (F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
      F4Chevalley.rootCurve _ 1)⁻¹
  simp [mul_inv_rev, F4Chevalley.rootCurve_inv, mul_assoc]

private theorem rankOneWordMatrix_square (i : typeF4RootPairing_base.support) (u : Fˣ) :
    (rankOneWordMatrix (F := F) (i : F4Chevalley.Root) (u ^ 2)) =
      (diag i u)⁻¹ * (rankOneWordMatrix (F := F) (i : F4Chevalley.Root) 1) * diag i u := by
  change F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ *
    F4Chevalley.rootCurve _ _ =
    (diag i u)⁻¹ * (F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
    F4Chevalley.rootCurve _ 1) * diag i u
  symm
  calc
    _ = ((diag i u)⁻¹ * F4Chevalley.rootCurve (i : F4Chevalley.Root) 1 * diag i u) *
        ((diag i u)⁻¹ * F4Chevalley.rootCurve (-(i : F4Chevalley.Root)) (-1⁻¹) * diag i u) *
        ((diag i u)⁻¹ * F4Chevalley.rootCurve (i : F4Chevalley.Root) 1 * diag i u) := by group
    _ = _ := by simp [diag_root]

private theorem torus_square (i : typeF4RootPairing_base.support) (u : Fˣ) :
    (corootWordMatrix (F := F) (i : F4Chevalley.Root) (u ^ 2)) = (diag i (u ^ 2))⁻¹ := by
  change (rankOneWordMatrix (F := F) _ (u ^ 2)) * (rankOneWordMatrix (F := F) _ (-1)) = _
  rw [rankOneWordMatrix_square, rankOneWordMatrix_neg_one]
  change (diag i u)⁻¹ * (rankOneWordMatrix (F := F) _ 1) * diag i u *
    ((rankOneWordMatrix (F := F) _ 1))⁻¹ = _
  rw [rankOneWordMatrix_one, mul_assoc (diag i u)⁻¹, diag_tits]
  rw [pow_two, diag_mul, mul_inv_rev]
  group


variable [Finite F] [CharP F 2]

private theorem unit_square_surjective (t : Fˣ) : ∃ u : Fˣ, u ^ 2 = t := by
  apply Finite.surjective_of_injective (f := fun u : Fˣ => u ^ 2) _ t
  intro u v huv
  apply Units.ext
  exact CharTwo.sq_injective (congrArg Units.val huv)

private theorem coroot_coe (i : typeF4RootPairing_base.support) (t : Fˣ) :
    (corootWord i.val (t : F)).val = (diag i t)⁻¹ := by
  obtain ⟨u,rfl⟩ := unit_square_surjective t
  exact torus_square i u

private theorem coroot_root (i : typeF4RootPairing_base.support) (u : Fˣ)
    (r : F4Chevalley.Root) (t : F) :
    corootWord i.val (u : F) * root r t * (corootWord i.val (u : F))⁻¹ =
      root r (((u ^ typeF4RootPairing.pairingIn ℤ r i.val : Fˣ) : F) * t) := by
  apply Subtype.ext
  change (corootWord i.val (u : F)).val * F4Chevalley.rootCurve r t *
    ((corootWord i.val (u : F)).val)⁻¹ = _
  rw [coroot_coe, inv_inv]
  exact integralChevalleyRootCurve_simpleCoroot_conjugation i u r t


omit [Finite F] [CharP F 2] in
private theorem simple_root_mem_levi (i : Fin 4) (hi : i.val < 2) (t : F) :
    root (typeF4SimpleRootIndex i) t ∈ longLevi F :=
  subset_closure ⟨i,t,hi,Or.inl rfl⟩

omit [Finite F] [CharP F 2] in
private theorem negative_simple_root_mem_levi (i : Fin 4) (hi : i.val < 2) (t : F) :
    root (-typeF4SimpleRootIndex i) t ∈ longLevi F :=
  subset_closure ⟨i,t,hi,Or.inr rfl⟩

omit [Finite F] [CharP F 2] in
private theorem coroot_mem_levi (i : Fin 4) (hi : i.val < 2) (t : F) :
    corootWord (typeF4SimpleRootIndex i) t ∈ longLevi F := by
  have hw (u : F) : rankOneWord (typeF4SimpleRootIndex i) u ∈ longLevi F :=
    mul_mem (mul_mem (simple_root_mem_levi i hi u)
      (negative_simple_root_mem_levi i hi _)) (simple_root_mem_levi i hi u)
  exact mul_mem (hw t) (hw (-1))

private theorem exists_scalar (hq : 2 < Nat.card F) : ∃ u : Fˣ, (u : F) ^ 2 ≠ 1 := by
  let := Fintype.ofFinite F
  have hex : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
    by_contra! hh
    obtain ⟨a,b,c,hab,hac,hbc⟩ := Fintype.two_lt_card_iff.mp
      (show 2 < Fintype.card F by simpa only [Nat.card_eq_fintype_card] using hq)
    have hc (x : F) : x = 0 ∨ x = 1 := by
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (hh x hx)
    rcases hc a with rfl | rfl <;> rcases hc b with rfl | rfl <;>
      rcases hc c with rfl | rfl <;> contradiction
  obtain ⟨a,ha0,ha1⟩ := hex
  refine ⟨Units.mk0 a ha0,?_⟩
  intro he
  exact ha1 (CharTwo.sq_injective (by simpa using he : a ^ 2 = (1 : F) ^ 2))

omit [Finite F] [CharP F 2] in
private theorem root_commutator (g : Ambient F) (r : F4Chevalley.Root) (t k : F)
    (h : g * root r t * g⁻¹ = root r (k*t)) :
    ⁅g,root r t⁆ = root r ((k-1)*t) := by
  rw [commutatorElement_def, h]
  apply Subtype.ext
  change F4Chevalley.rootCurve r (k*t) * (F4Chevalley.rootCurve r t)⁻¹ = _
  rw [F4Chevalley.rootCurve_inv, ← F4Chevalley.rootCurve_add]
  congr 1
  ring

/-- Every field parameter occurs in the commutator subgroup of the literal
long A₂ Levi. The nonbinary hypothesis is used to choose a nontrivial coroot scalar. -/
theorem longLevi_perfect (hq : 2 < Nat.card F) : Group.IsPerfect (longLevi F) := by
  obtain ⟨u,hu⟩ := exists_scalar hq
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (commutator_le_self _)
  apply (closure_le _).mpr
  rintro x ⟨i,t,hi,hx⟩
  let s : F := t / ((u : F)^2 - 1)
  have hs : ((u : F)^2 - 1)*s = t := by
    dsimp [s]
    exact mul_div_cancel₀ t (sub_ne_zero.mpr hu)
  rcases hx with rfl | rfl
  · have hh := coroot_root (typeF4RootPairing_baseEquiv i) u
      (typeF4SimpleRootIndex i) s
    rw [← typeF4RootPairing_baseEquiv_val i] at hh
    simp only [RootPairing.pairingIn_same,zpow_ofNat,Units.val_pow_eq_pow_val,
      typeF4RootPairing_baseEquiv_val] at hh
    have he := root_commutator _ _ _ _ hh
    rw [hs] at he
    rw [← he]
    exact commutator_mem_commutator (coroot_mem_levi i hi _)
      (simple_root_mem_levi i hi _)
  · have hh := coroot_root (typeF4RootPairing_baseEquiv i) u⁻¹
      (-typeF4SimpleRootIndex i) s
    have hp : typeF4RootPairing.pairingIn ℤ (-typeF4SimpleRootIndex i)
        (typeF4RootPairing_baseEquiv i).val = -2 := by
      rw [← typeF4RootPairing_baseEquiv_val i, RootPairing.indexNeg_neg,
        RootPairing.pairingIn_reflectionPerm_self_left, RootPairing.pairingIn_same]
    rw [hp] at hh
    simp only [zpow_neg,zpow_ofNat,inv_pow,inv_inv,
      Units.val_pow_eq_pow_val,typeF4RootPairing_baseEquiv_val] at hh
    have he := root_commutator _ _ _ _ hh
    rw [hs] at he
    rw [← he]
    exact commutator_mem_commutator (coroot_mem_levi i hi _)
      (negative_simple_root_mem_levi i hi _)

omit [Finite F] [CharP F 2] in
/-- The component candidate lies in the original parabolic. -/
theorem component_le_parabolic : componentCandidate F ≤ parabolic F := by
  rw [← component_join_positive]
  exact le_sup_left

omit [Finite F] [CharP F 2] in
/-- Normality is relative to the original parabolic, with all field parameters. -/
theorem positive_normalizes_component :
    positive F ≤ normalizer (componentCandidate F : Set (Ambient F)) := by
  apply le_normalizer_iff.mpr
  intro u hu x hx
  let f := (MulAut.conj u).toMonoidHom
  have hA : (longLevi F).map f ≤ componentCandidate F := by
    rintro _ ⟨a,ha,rfl⟩
    change u * a * u⁻¹ ∈ componentCandidate F
    have hh := (componentCandidate F).mul_mem
      (mem_sup_right (commutator_mem_commutator hu ha)) (mem_sup_left ha)
    simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hh
  have hD : (⁅positive F,longLevi F⁆).map f ≤ ⁅positive F,longLevi F⁆ :=
    (mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_left _ _ hu)).le
  have hm : (componentCandidate F).map f ≤ componentCandidate F := by
    rw [componentCandidate, Subgroup.map_sup]
    exact sup_le hA (hD.trans le_sup_right)
  exact hm (mem_map_of_mem f hx)

omit [Finite F] [CharP F 2] in
/-- Normality inside the literal parabolic, without a component-classification premise. -/
theorem component_normal : ((componentCandidate F).subgroupOf (parabolic F)).Normal :=
  (normal_subgroupOf_iff_le_normalizer component_le_parabolic).mpr
    (sup_le positive_normalizes_component
      ((le_sup_left : longLevi F ≤ componentCandidate F).trans
        (componentCandidate F).le_normalizer))


/-- The candidate quotient by its normal component is a two-group. This
uses the literal positive subgroup as supplement, not a Sylow assumption. -/
theorem parabolic_component_quotient_isPGroup :
    let := component_normal (F := F)
    IsPGroup 2 (parabolic F ⧸ (componentCandidate F).subgroupOf (parabolic F)) := by
  let := component_normal (F := F)
  apply isPGroup_quotient_of_sup_eq_top
    ((componentCandidate F).subgroupOf (parabolic F))
    ((positive F).subgroupOf (parabolic F)) positive_isPGroup.comap_subtype
  apply map_injective (parabolic F).subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le component_le_parabolic,
    map_subgroupOf_eq_of_le (show positive F ≤ parabolic F from le_sup_left),
    component_join_positive, ← MonoidHom.range_eq_map, range_subtype]

/-- The original component candidate is exactly the embedded solvable residual
of the original field-valued parabolic. -/
theorem component_eq_solvableResidual (hq : 2 < Nat.card F) :
    componentCandidate F = (solvableResidual (parabolic F)).map (parabolic F).subtype := by
  let := component_normal (F := F)
  let := longLevi_perfect hq
  let : Group.IsNilpotent
      (parabolic F ⧸ (componentCandidate F).subgroupOf (parabolic F)) :=
    parabolic_component_quotient_isPGroup.isNilpotent
  let D := (solvableResidual (parabolic F)).map (parabolic F).subtype
  have hAD : longLevi F ≤ D :=
    le_map_solvableResidual_of_isPerfect _ _ le_sup_right
  have hUN : positive F ≤ normalizer (D : Set (Ambient F)) :=
    (le_sup_left : positive F ≤ parabolic F).trans
      ((parabolic F).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (parabolic F)
          (solvableResidual (parabolic F))))
  apply le_antisymm
  · exact sup_le hAD ((commutator_mono le_rfl hAD).trans
      (le_normalizer_iff_commutator_le_right.mp hUN))
  · simpa only [map_subgroupOf_eq_of_le component_le_parabolic] using
      map_mono (f := (parabolic F).subtype)
        (solvableResidual_le_of_solvable_quotient
          ((componentCandidate F).subgroupOf (parabolic F)))

/-- Perfectness of the actual original candidate, including all field-four parameters. -/
theorem component_perfect (hq : 2 < Nat.card F) : Group.IsPerfect (componentCandidate F) := by
  rw [component_eq_solvableResidual hq]
  exact Group.IsPerfect.map (parabolic F).subtype

/-- The candidate is also the actual two-residual. The equality distinguishes
this residual from the two-core needed in the still-open quotient calculation. -/
theorem component_eq_twoResidual (hq : 2 < Nat.card F) :
    componentCandidate F = (pResidual 2 (parabolic F)).map (parabolic F).subtype := by
  let := component_perfect hq
  have he := pResidual_eq_solvableResidual_of_perfect_sup_twoGroup
    (componentCandidate F) (positive F) positive_isPGroup positive_normalizes_component
  rw [component_join_positive] at he
  rw [he]
  exact component_eq_solvableResidual hq

/-- Field four supplies perfectness, relative normality, the literal residual
identity and MS3 simultaneously on the original matrix subgroups. The quotient,
fitting, SQTK and odd-index radical clauses are not assumed or asserted. -/
theorem field_four_residual_input :
    Group.IsPerfect (componentCandidate FourField) ∧
    ((componentCandidate FourField).subgroupOf (parabolic FourField)).Normal ∧
    componentCandidate FourField =
      (solvableResidual (parabolic FourField)).map (parabolic FourField).subtype ∧
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.MSNoCharacteristicNormal
      (componentCandidate FourField) (positive FourField) := by
  have hq : 2 < Nat.card FourField := by rw [fourField_card]; decide
  exact ⟨component_perfect hq,component_normal,component_eq_solvableResidual hq,candidate_ms3⟩

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.F4Original
