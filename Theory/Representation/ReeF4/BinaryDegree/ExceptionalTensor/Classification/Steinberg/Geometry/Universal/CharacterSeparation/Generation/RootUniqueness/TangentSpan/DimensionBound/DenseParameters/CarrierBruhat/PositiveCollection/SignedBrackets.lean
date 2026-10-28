module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.CarrierBruhat.PositiveCollection.IntegralB2
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RootSums.RootSpace
public import Theory.AlgebraicGroup.RootSystems.IntegralChevalleyOperatorOrientation

/-!
# Signed integral B₂ operator brackets

For positive F4 roots whose sum is a root, the commutator of their canonical
integral operators is a sign times the root-string coefficient `p + 1` times
the sum-root operator. Root-weight addition and multiplicity one first put the
commutator in that integral operator line. Cartan columns then determine its
coefficient: the simple-root orientation signs convert Geck's absolute Cartan
entries to signed pairings, and the two root pairings are linearly independent.
This proves an operator identity over ℤ from the signed vector-action formula.

For a long root `r` and short root `s` with inner product `-1`, the squared
length of `r - s` is five, so the bottom coefficient at `(s,r)` is zero.
Moving one step along the string gives bottom coefficient one at `(s,r+s)`.
Thus the two B₂ coefficients have magnitudes one and two, respectively.

Sources: Geck's integral construction and the root-space argument in
`RootSums.RootSpace`, the vector-action theorem in `IntegralChevalleyBrackets`,
and the orientation in `IntegralChevalleyOperatorOrientation`. This is the
B₂ Chevalley calculation used for the Ree radical coordinates underlying
Aschbacher–Smith F.1.12(I)(5), `refs/quasithin.pdf`, printed p.263 (PDF p.274).
The root-curve and B₂ block-swap assembly is separate.
-/

public section

open scoped Matrix
open ReeF4 Theory.AlgebraicGroup StandardRootSystem RootPairing.IntegralGeckConstruction

namespace Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat.CollectionMatrices
noncomputable section
namespace SignedBrackets
set_option linter.unusedSectionVars false
section General
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] {b : P.Base} [Fintype ι] [DecidableEq ι]

private lemma oriented_cartan (i j : b.support) :
    |b.cartanMatrix i j| =
      simpleOperatorOrientation i * simpleOperatorOrientation j * b.cartanMatrix i j := by
  by_cases hij : i = j
  · subst j
    rw [simpleOperatorOrientation_sq, one_mul, RootPairing.Base.cartanMatrix_apply_same]
    norm_num
  · by_cases h : b.cartanMatrix i j = 0
    · simp [h]
    · rw [simpleOperatorOrientation_mul_eq_neg_one_of_cartan_ne_zero i j hij h,
        abs_of_nonpos (b.cartanMatrix_le_zero_of_ne i j hij)]
      ring

private lemma pairing_reflection (i : b.support) (r : ι) (j : b.support) :
    P.pairingIn ℤ (P.reflectionPerm i r) j =
      P.pairingIn ℤ r j - P.pairingIn ℤ r i * b.cartanMatrix i j := by
  apply FaithfulSMul.algebraMap_injective ℤ R
  simp only [map_sub, map_mul, P.algebraMap_pairingIn,
    RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  change P.toLinearMap (P.root (P.reflectionPerm i r)) (P.coroot j) = _
  rw [P.root_reflectionPerm, P.reflection_apply_root]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    P.root_coroot_eq_pairing, smul_eq_mul]

private lemma titsLiftInv_cartan (i j : b.support) :
    titsLiftInv (P := P) i *ᵥ u j = u j - |b.cartanMatrix i j| • u i := by
  have h2 : titsLift (P := P) i *ᵥ (titsLift i *ᵥ u j) = u j := by
    rw [titsLift_mulVec_u, Matrix.mulVec_sub, Matrix.mulVec_smul,
      titsLift_mulVec_u, titsLift_mulVec_u]
    norm_num only [RootPairing.Base.cartanMatrix_apply_same,
      abs_of_pos (by norm_num : (0 : ℤ) < 2)]
    module
  have h := congrArg (fun x => titsLiftInv (P := P) i *ᵥ x) h2
  rw [Matrix.mulVec_mulVec, titsLift_inv_mul, Matrix.one_mulVec] at h
  exact h.symm.trans (titsLift_mulVec_u i j)

private lemma transported_cartan (w : List b.support) (k j : b.support) :
    transportedMatrix w (eMatrix k) *ᵥ u j =
      (simpleOperatorOrientation k * simpleOperatorOrientation j *
        P.pairingIn ℤ (reflectionWord w k) j) • transportedVector w (v k) := by
  induction w generalizing j with
  | nil =>
    simpa only [transportedMatrix, transportedVector, titsWord, titsWordInv_nil,
      one_mul, mul_one, Matrix.one_mulVec, reflectionWord,
      RootPairing.Base.cartanMatrixIn_def] using
      (eMatrix_mulVec_u (P := P) k j).trans (congrArg (fun n : ℤ => n • v (b := b) k)
        (oriented_cartan k j))
  | cons i w ih =>
    have hmatrix : transportedMatrix (i :: w) (eMatrix k) =
        titsLift i * transportedMatrix w (eMatrix k) * titsLiftInv i := by
      simp only [transportedMatrix, titsWord, titsWordInv_cons]
      noncomm_ring
    rw [hmatrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      titsLiftInv_cartan, Matrix.mulVec_sub, Matrix.mulVec_smul, ih j, ih i]
    simp only [Matrix.mulVec_smul, smul_smul, ← sub_smul]
    simp only [transportedVector, titsWord, ← Matrix.mulVec_mulVec]
    rw [reflectionWord, pairing_reflection, oriented_cartan]
    congr 1
    have hi := simpleOperatorOrientation_sq (b := b) i
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hi with hi | hi <;> rw [hi] <;> ring

private lemma positive_cartan (r : ι) (hr : b.IsPos r) (j : b.support) :
    rootOperator r *ᵥ u j =
      (simpleOperatorOrientation (rootRoute (P := P) (b := b) r).simple *
        simpleOperatorOrientation j * P.pairingIn ℤ r j) • rootVector r := by
  rw [rootOperator_of_pos r hr, rootVector_of_pos r hr]
  simpa only [(rootRoute (P := P) (b := b) r).target] using
    transported_cartan (rootRoute (P := P) (b := b) r).word
      (rootRoute (P := P) (b := b) r).simple j

private lemma pairings_independent (a b' : ι)
    (hlin : LinearIndependent R ![P.root a, P.root b']) (x y : ℤ)
    (h : ∀ j : b.support, x * P.pairingIn ℤ a j + y * P.pairingIn ℤ b' j = 0) :
    x = 0 ∧ y = 0 := by
  have hz : (x : R) • P.root a + (y : R) • P.root b' = 0 := by
    apply P.toPerfPair.injective
    change P.toLinearMap ((x : R) • P.root a + (y : R) • P.root b') = P.toLinearMap 0
    rw [map_zero]
    apply LinearMap.ext_on (s := P.coroot '' b.support) (by
      rw [b.span_coroot_support]
      exact RootPairing.IsRootSystem.span_coroot_eq_top)
    rintro _ ⟨j, hj, rfl⟩
    have hh := congrArg (algebraMap ℤ R) (h ⟨j, hj⟩)
    simp only [map_add, map_mul, map_zero, P.algebraMap_pairingIn] at hh
    simp only [algebraMap_int_eq, Int.coe_castRingHom] at hh
    simpa only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      P.root_coroot_eq_pairing, LinearMap.zero_apply] using hh
  obtain ⟨hx, hy⟩ := (LinearIndependent.pair_iff.mp hlin) (x : R) (y : R) hz
  exact ⟨Int.cast_eq_zero.mp hx, Int.cast_eq_zero.mp hy⟩

private lemma bracket_coefficient (a b' c : ι)
    (ha : b.IsPos a) (hb : b.IsPos b') (hc : b.IsPos c)
    (hroot : P.root c = P.root a + P.root b')
    (hline : ∃ n : ℤ, rootOperator a * rootOperator b' - rootOperator b' * rootOperator a =
      n • rootOperator (P := P) (b := b) c) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧
      rootOperator a * rootOperator b' - rootOperator b' * rootOperator a =
        (ε * (P.chainBotCoeff a b' + 1 : ℤ)) • rootOperator (P := P) (b := b) c := by
  obtain ⟨n, hn⟩ := hline
  obtain ⟨e, he, hab⟩ := rootOperator_mulVec_root_add_signed (b := b) hroot
  obtain ⟨f, _, hba⟩ := rootOperator_mulVec_root_add_signed (b := b)
    (hroot.trans (add_comm _ _))
  let sa := simpleOperatorOrientation (rootRoute (P := P) (b := b) a).simple
  let sb := simpleOperatorOrientation (rootRoute (P := P) (b := b) b').simple
  let sc := simpleOperatorOrientation (rootRoute (P := P) (b := b) c).simple
  have hsc : sc * sc = 1 := simpleOperatorOrientation_sq _
  have hsb : sb * sb = 1 := simpleOperatorOrientation_sq _
  obtain ⟨vsign, hvs, hv⟩ := exists_rootVector_sign (P := P) (b := b) c
  have hvs0 : vsign ≠ 0 := by intro hz; simp [hz] at hvs
  have hcoeff (j : b.support) :
      (n * sc + sa * f * (P.chainBotCoeff b' a + 1 : ℤ)) * P.pairingIn ℤ a j +
        (n * sc - sb * e * (P.chainBotCoeff a b' + 1 : ℤ)) * P.pairingIn ℤ b' j = 0 := by
    have h := congrArg (fun A => A *ᵥ u j) hn
    simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      positive_cartan a ha, positive_cartan b' hb, positive_cartan c hc,
      Matrix.mulVec_smul, hab, hba, smul_smul] at h
    rw [hv] at h
    have hj := congrFun h (Sum.inr c)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, v, Pi.single_eq_same, mul_one] at hj
    rw [RootPairing.pairingIn_eq_add_of_root_eq_add (S := ℤ) hroot] at hj
    have hs := simpleOperatorOrientation_sq (b := b) j
    change (sb * _ * _) * (e * _) * vsign - (sa * _ * _) * (f * _) * vsign =
      (n * (sc * _ * (_ + _))) * vsign at hj
    rw [← sub_mul] at hj
    have hz := sub_eq_zero.mpr (mul_right_cancel₀ hvs0 hj)
    have hs0 : simpleOperatorOrientation j ≠ 0 := by intro h0; simp [h0] at hs
    apply (mul_eq_zero.mp (show simpleOperatorOrientation j *
      ((n * sc + sa * f * (P.chainBotCoeff b' a + 1 : ℤ)) * P.pairingIn ℤ a j +
        (n * sc - sb * e * (P.chainBotCoeff a b' + 1 : ℤ)) * P.pairingIn ℤ b' j) = 0 from ?_)).resolve_left hs0
    linear_combination -hz
  have hlin := P.linearIndependent_of_add_mem_range_root' ⟨c, hroot⟩
  have hn' := (pairings_independent a b' hlin _ _ hcoeff).2
  have hnval : n = sc * sb * e * (P.chainBotCoeff a b' + 1 : ℤ) := by
    linear_combination sc * hn' - n * hsc
  refine ⟨sc * sb * e, ?_, ?_⟩
  · calc
      (sc * sb * e) ^ 2 = (sc * sc) * (sb * sb) * (e * e) := by ring
      _ = 1 := by rw [hsc, hsb, he]; norm_num
  · rw [hn, hnval]

end General

section RootLine
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι R M N : Type*} [Field R] [CharZero R] [IsAlgClosed R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private lemma transported_bracket_line
    (w z t : List b.support) (i j k : b.support)
    (hroot : P.root (reflectionWord t k) =
      P.root (reflectionWord w i) + P.root (reflectionWord z j)) :
    ∃ n : ℤ,
      titsConjugate w (eMatrix i) * titsConjugate z (eMatrix j) -
        titsConjugate z (eMatrix j) * titsConjugate w (eMatrix i) =
          n • titsConjugate t (eMatrix k) := by
  let E := (titsConjugate w (eMatrix i)).map (algebraMap ℤ R)
  let B := (titsConjugate z (eMatrix j)).map (algebraMap ℤ R)
  let A := titsConjugate w (eMatrix i) * titsConjugate z (eMatrix j) -
    titsConjugate z (eMatrix j) * titsConjugate w (eMatrix i)
  have hA : A.map (algebraMap ℤ R) = ⁅E, B⁆ := by
    simp only [A, E, B, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Ring.lie_def]
  have hEmem : E ∈ RootPairing.GeckConstruction.lieAlgebra b := by
    apply map_titsConjugate_mem_lieAlgebra
    rw [map_eMatrix]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra i
  have hBmem : B ∈ RootPairing.GeckConstruction.lieAlgebra b := by
    apply map_titsConjugate_mem_lieAlgebra
    rw [map_eMatrix]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra j
  have hAweight : HasRootWeight (P := P) (b := b) (reflectionWord t k)
      (A.map (algebraMap ℤ R)) := by
    rw [hA]
    intro l
    rw [leibniz_lie, map_titsConjugate_hasRootWeight (P := P) w i l,
      map_titsConjugate_hasRootWeight (P := P) z j l,
      smul_lie, lie_smul, ← add_smul,
      RootPairing.pairing_eq_add_of_root_eq_add hroot]
  exact ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple.RootSumSpace.integral_matrix_eq_smul_titsConjugate_of_weight (P := P) A t k
    (by rw [hA]; exact (RootPairing.GeckConstruction.lieAlgebra b).lie_mem hEmem hBmem)
    hAweight
end RootLine

private lemma extension_root_add {r s c : typeF4Roots}
    (h : typeF4RootPairing.root c = typeF4RootPairing.root r + typeF4RootPairing.root s) :
    (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root c =
      (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root r +
        (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root s := by
  have hs : typeF4RootPairing.rootSpanMem ℤ c =
      typeF4RootPairing.rootSpanMem ℤ r + typeF4RootPairing.rootSpanMem ℤ s :=
    Subtype.ext h
  change scalarExtensionRoot c = scalarExtensionRoot r + scalarExtensionRoot s
  ext l
  simp only [scalarExtensionRoot, hs, map_add, Finsupp.add_apply, Pi.add_apply]

private lemma positive_bracket_mem_line (a b c : F4Chevalley.Root)
    (ha : typeF4RootPairing_base.IsPos a) (hb : typeF4RootPairing_base.IsPos b)
    (hc : typeF4RootPairing_base.IsPos c)
    (hroot : typeF4RootPairing.root c = typeF4RootPairing.root a + typeF4RootPairing.root b) :
    ∃ n : ℤ, rootOperator a * rootOperator b - rootOperator b * rootOperator a =
      n • rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) c := by
  let w := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) a
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) b
  let t := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) c
  have hroot' := extension_root_add hroot
  rw [← w.target, ← z.target, ← t.target,
    ← scalarExtension_reflectionWord (b := typeF4RootPairing_base) w.word w.simple,
    ← scalarExtension_reflectionWord (b := typeF4RootPairing_base) z.word z.simple,
    ← scalarExtension_reflectionWord (b := typeF4RootPairing_base) t.word t.simple] at hroot'
  obtain ⟨n, hn⟩ := transported_bracket_line
    (P := scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base))
    (b := scalarExtensionBase (P := typeF4RootPairing) (b := typeF4RootPairing_base))
    w.word z.word t.word w.simple z.simple t.simple hroot'
  simp only [scalarExtension_eMatrix, scalarExtension_titsConjugate] at hn
  refine ⟨n, ?_⟩
  rw [rootOperator_of_pos a ha, rootOperator_of_pos b hb, rootOperator_of_pos c hc]
  exact hn

/-- The signed Chevalley coefficient for the commutator of actual positive
integral F4 root operators. -/
theorem positive_operator_bracket_signed (a b c : F4Chevalley.Root)
    (ha : typeF4RootPairing_base.IsPos a) (hb : typeF4RootPairing_base.IsPos b)
    (hroot : c.val = a.val + b.val) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧
      F4Chevalley.integralOperators.rootOperator a * F4Chevalley.integralOperators.rootOperator b -
        F4Chevalley.integralOperators.rootOperator b * F4Chevalley.integralOperators.rootOperator a =
          (ε * (typeF4RootPairing.chainBotCoeff a b + 1 : ℤ)) •
            F4Chevalley.integralOperators.rootOperator c := by
  have h : typeF4RootPairing.root c = typeF4RootPairing.root a + typeF4RootPairing.root b := hroot
  have hc := ha.add hb h
  exact bracket_coefficient a b c ha hb hc h (positive_bracket_mem_line a b c ha hb hc h)

private lemma short_long_chainBotCoeff (r s : F4Chevalley.Root)
    (hl : IsLongRoot r) (hs : IsShortRoot s) (hdot : dot r.val s.val = -1) :
    typeF4RootPairing.chainBotCoeff s r = 0 := by
  apply typeF4RootPairing.chainBotCoeff_eq_zero_iff.mpr
  right
  rintro ⟨t, ht⟩
  have hnorm : dot (r.val - s.val) (r.val - s.val) = 5 := by
    have hsr : dot s.val r.val = -1 := by simpa only [dot, mul_comm] using hdot
    change (r.val - s.val) ⬝ᵥ (r.val - s.val) = 5
    simp only [sub_dotProduct, dotProduct_sub]
    change dot r.val r.val - dot s.val r.val -
      (dot r.val s.val - dot s.val s.val) = 5
    rw [isLongRoot_norm r hl, isShortRoot_norm s hs, hdot, hsr]
    norm_num
  have hb : dot t.val t.val ≤ 2 := by
    by_cases h : IsLongRoot t
    · rw [isLongRoot_norm t h]
    · rw [isShortRoot_norm t h]; norm_num
  change t.val = r.val - s.val at ht
  rw [ht, hnorm] at hb
  norm_num at hb

end SignedBrackets

/-- The two signed integral operator brackets in a positive B₂ root block.
The coefficients have magnitudes one and two before specialization. -/
theorem b2BracketRelations (r s c d : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (hl : IsLongRoot r) (hshort : IsShortRoot s)
    (hdot : dot r.val s.val = -1)
    (hc : c.val = r.val + s.val)
    (hd : d.val = r.val + (2 : ℝ) • s.val) : B2BracketRelations r s c d := by
  have hcp : typeF4RootPairing_base.IsPos c := hr.add hs hc
  have hsc : c.val = s.val + r.val := hc.trans (add_comm _ _)
  have hsd : d.val = s.val + c.val := by rw [hd, hc, two_smul]; abel
  have hbot := SignedBrackets.short_long_chainBotCoeff r s hl hshort hdot
  have hlin := typeF4RootPairing.linearIndependent_of_add_mem_range_root' ⟨c, hsc⟩
  have hbot' : typeF4RootPairing.chainBotCoeff s c = 1 := by
    rw [typeF4RootPairing.chainBotCoeff_of_add hlin hc, hbot]
  obtain ⟨ε, hε, he⟩ := SignedBrackets.positive_operator_bracket_signed s r c hs hr hsc
  obtain ⟨δ, hδ, hδeq⟩ := SignedBrackets.positive_operator_bracket_signed s c d hs hcp hsd
  refine ⟨⟨ε, hε, ?_⟩, ⟨δ, hδ, ?_⟩⟩
  · simpa only [hbot, Nat.cast_zero, zero_add, mul_one] using he
  · simpa only [hbot', Nat.cast_one, one_add_one_eq_two, mul_comm δ 2] using hδeq

end
end Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat.CollectionMatrices
