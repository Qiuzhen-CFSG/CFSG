module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.TorusRecovery
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.NormalizerCosets
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Literal simple words for the F4 normalizer

Every rank-one normalizer word is a product of four direct coroots followed
by a literal list of parameter-one simple normalizer elements. The diagonal
normalization and signed-route calculations below are adapted from the private
matrix calculations of `DenseParameters.NormalizerCosets`, preserving that
module's public boundary. In characteristic two each simple lift is its own
inverse, so subgroup words are actual positive list products.

Source: Steinberg, *Lectures on Chevalley Groups*, Lemmas 5–6 and Theorem 4′,
`refs/KGroup/GLS3/Chapter2St1.tex`.
-/

public section
noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open F4Chevalley F4Chevalley.DenseParameters
open RootPairing.IntegralGeckConstruction ReeF4.WordRelations
open ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport
open scoped Matrix Pointwise
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.RestrictedCells
local instance restrictedNormalizerRootNeg : InvolutiveNeg Root := typeF4RootPairing.indexNeg
private abbrev MatrixUnit (S : Type*) [CommRing S] :=
  (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex S)ˣ

private def matrixRankOne {S : Type*} [CommRing S] (r : F4Chevalley.Root) (t : Sˣ) :
    MatrixUnit S :=
  F4Chevalley.rootCurve r (t : S) * F4Chevalley.rootCurve (-r) (-((t⁻¹ : Sˣ) : S)) *
    F4Chevalley.rootCurve r (t : S)

private theorem matrixRankOne_conjugate {S : Type*} [CommRing S]
    (n : MatrixUnit S) (r s : F4Chevalley.Root)
    (hp : ∀ a, n * F4Chevalley.rootCurve r a * n⁻¹ = F4Chevalley.rootCurve s a)
    (hn : ∀ a, n * F4Chevalley.rootCurve (-r) a * n⁻¹ = F4Chevalley.rootCurve (-s) a)
    (t : Sˣ) : matrixRankOne s t = n * matrixRankOne r t * n⁻¹ := by
  dsimp only [matrixRankOne]
  rw [← hp, ← hn]
  group

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- The actual faithful matrix map, with its comparison equations exposed here. -/
def literalMatrix : Variety.Point (Carrier (k := k)) →* (Matrix BasisIndex BasisIndex k)ˣ :=
  matrixAmbientEquiv.symm.toMonoidHom.comp (ambientClosedCarrier (k := k)).inclusion.onPoints

theorem literalMatrix_injective : Function.Injective (literalMatrix (k := k)) :=
  matrixAmbientEquiv.symm.injective.comp (ambientClosedCarrier (k := k)).inclusion_injective

@[simp] theorem literalMatrix_root (r : Root) (t : k) :
    literalMatrix (rootElement r t) = rootCurve r t := by
  apply matrixAmbientEquiv.injective
  change matrixAmbientEquiv (matrixAmbientEquiv.symm _) = _
  rw [MulEquiv.apply_symm_apply]
  exact rootElement_inclusion r t

@[simp] theorem literalMatrix_algebraicRoot (r : Root) (t : k) :
    literalMatrix (algebraicRootElement r t) = rootCurve r t :=
  literalMatrix_root r t

private theorem literalMatrix_rankOne (r : Root) (t : kˣ) :
    literalMatrix (rankOne r t) = matrixRankOne r t := by
  simp only [rankOne, map_mul, literalMatrix_root, matrixRankOne]

@[simp] theorem literalMatrix_simpleN (i : Fin 4) :
    literalMatrix (algebraicNElement (typeF4SimpleRootIndex i) (1 : kˣ)) =
      titsUnit [typeF4RootPairing_baseEquiv i] := by
  simp only [algebraicNElement, map_mul, literalMatrix_algebraicRoot,
    titsUnit_cons, titsUnit_nil, mul_one, inv_one, Units.val_one,
    typeF4RootPairing_baseEquiv_val]

variable [CharP k 2]

private abbrev matrixTorus : Subgroup (MatrixUnit k) := (torusMatrixHom (F := k)).range

private abbrev matrixTits : Subgroup (MatrixUnit k) :=
  Subgroup.closure (Set.range fun i : typeF4RootPairing_base.support => titsUnit (S := k) [i])

private abbrev diag (i : typeF4RootPairing_base.support) (u : kˣ) :=
  integralChevalleyTorusElement (P := typeF4RootPairing)
    (integralChevalleySimpleCorootParameter i u)

omit [IsAlgClosed k] [CharP k 2] in
private theorem diag_mem (i : typeF4RootPairing_base.support) (u : kˣ) :
    diag i u ∈ matrixTorus (k := k) :=
  ⟨integralChevalleySimpleCorootParameter i u, rfl⟩

omit [IsAlgClosed k] [CharP k 2] in
private theorem basisUnit_simple (q : typeF4RootPairing_base.support)
    (u : kˣ) (a : BasisIndex) :
    chevalleyBasisTorusUnit (P := typeF4RootPairing)
      (integralChevalleySimpleCorootParameter q u) a =
      u ^ (-chevalleyBasisWeight (P := typeF4RootPairing) a q) := by
  unfold chevalleyBasisTorusUnit integralChevalleySimpleCorootParameter
  rw [Finset.prod_eq_single q]
  · simp
  · intro j _ hj; simp [hj]
  · simp

omit [IsAlgClosed k] [CharP k 2] in
private theorem weight_reflection (a : BasisIndex)
    (i q : F4Chevalley.Root) :
    chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4RootPairing.reflectionPerm i q) =
      chevalleyBasisWeight (P := typeF4RootPairing) a q -
        typeF4RootPairing.pairingIn ℤ i q * chevalleyBasisWeight (P := typeF4RootPairing) a i := by
  cases a with
  | inl j => simp [chevalleyBasisWeight]
  | inr r =>
    simp only [chevalleyBasisWeight, typeF4RootPairing.pairingIn_reflectionPerm]
    have hr : typeF4RootPairing.root (typeF4RootPairing.reflectionPerm i r) =
        (1 : ℤ) • typeF4RootPairing.root r +
          (-typeF4RootPairing.pairingIn ℤ r i) • typeF4RootPairing.root i := by
      rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root]
      simp [sub_eq_add_neg, ← typeF4RootPairing.algebraMap_pairingIn ℤ,
        Int.cast_smul_eq_zsmul]
    simpa [smul_eq_mul, sub_eq_add_neg, mul_comm] using
      (typeF4RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := q) hr)

omit [IsAlgClosed k] [CharP k 2] in
private theorem tits_simple_diag (i q : typeF4RootPairing_base.support)
    (u : kˣ) :
    titsUnit (S := k) [i] * diag q u =
      (diag q u * diag i (u ^ (-typeF4RootPairing.pairingIn ℤ i q))) *
        titsUnit (S := k) [i] := by
  apply Units.ext
  change specializeMatrix (titsWord [i]) * Matrix.diagonal _ =
    (Matrix.diagonal _ * Matrix.diagonal _) * specializeMatrix (titsWord [i])
  simp only [titsWord, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  ext row col
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : titsLift i row col = 0
  · simp [specializeMatrix, hz]
  · have hw := titsLift_respectsChevalleyGrading i row col hz
      (typeF4RootPairing.reflectionPerm i q)
    rw [typeF4RootPairing.reflectionPerm_self, weight_reflection] at hw
    have hu : chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter q u) col =
        chevalleyBasisTorusUnit (P := typeF4RootPairing)
          (integralChevalleySimpleCorootParameter q u) row *
        chevalleyBasisTorusUnit (P := typeF4RootPairing)
          (integralChevalleySimpleCorootParameter i
            (u ^ (-typeF4RootPairing.pairingIn ℤ i q))) row := by
      rw [basisUnit_simple, basisUnit_simple, basisUnit_simple, ← zpow_mul, ← zpow_add]
      congr 1
      rw [← hw]
      ring
    rw [hu, Units.val_mul]
    exact mul_comm _ _



omit [IsAlgClosed k] in
private theorem simple_lift_inv (i : typeF4RootPairing_base.support) :
    (titsUnit (S := k) [i])⁻¹ = titsUnit [i] := by
  rw [titsUnit_cons, titsUnit_nil, mul_one]
  simp only [mul_inv_rev, rootCurve_inv, CharTwo.neg_eq]
  group

omit [IsAlgClosed k] [CharP k 2] in
private theorem simple_conj_torus_mem (i : typeF4RootPairing_base.support)
    (u : typeF4RootPairing_base.support → kˣ) :
    titsUnit [i] * torusMatrixHom u * (titsUnit [i])⁻¹ ∈ matrixTorus (k := k) := by
  let C := (matrixTorus (k := k)).comap
    ((MulAut.conj (titsUnit [i])).toMonoidHom.comp torusMatrixHom)
  change u ∈ C
  have hu : u = ∏ q, integralChevalleySimpleCorootParameter q (u q) := by
    funext j
    simp [integralChevalleySimpleCorootParameter, Finset.prod_apply]
  rw [hu]
  apply C.prod_mem
  intro q _
  change titsUnit [i] * diag q (u q) * (titsUnit [i])⁻¹ ∈ matrixTorus (k := k)
  rw [tits_simple_diag, mul_assoc, mul_inv_cancel, mul_one]
  exact (matrixTorus (k := k)).mul_mem (diag_mem q (u q)) (diag_mem i _)

omit [IsAlgClosed k] in
private theorem simple_mem_normalizer (i : typeF4RootPairing_base.support) :
    titsUnit (S := k) [i] ∈ Subgroup.normalizer (matrixTorus (k := k) : Set (MatrixUnit k)) := by
  have hconj (x : MatrixUnit k) (hx : x ∈ matrixTorus (k := k)) :
      titsUnit [i] * x * (titsUnit [i])⁻¹ ∈ matrixTorus (k := k) := by
    obtain ⟨u, rfl⟩ := hx
    exact simple_conj_torus_mem i u
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj x
  · intro hx
    have hh := hconj _ hx
    have he : titsUnit [i] * (titsUnit [i] * x * (titsUnit [i])⁻¹) *
        (titsUnit [i])⁻¹ = x := by
      calc
        _ = (titsUnit [i])⁻¹ * (titsUnit [i] * x * (titsUnit [i])⁻¹) *
            titsUnit [i] := by simp only [simple_lift_inv]
        _ = x := by group
    rwa [he] at hh

omit [IsAlgClosed k] in
private theorem matrixTits_le_normalizer :
    matrixTits (k := k) ≤ Subgroup.normalizer (matrixTorus (k := k) : Set (MatrixUnit k)) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact simple_mem_normalizer i

omit [IsAlgClosed k] [CharP k 2] in
private theorem word_mem_matrixTits (w : List typeF4RootPairing_base.support) :
    titsUnit (S := k) w ∈ matrixTits (k := k) := by
  induction w with
  | nil => simp only [titsUnit_nil]; exact (matrixTits (k := k)).one_mem
  | cons i w ih =>
    have he : titsUnit (S := k) (i :: w) = titsUnit [i] * titsUnit w := by
      rw [titsUnit_cons, titsUnit_cons, titsUnit_nil, mul_one]
    rw [he]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) ih

omit [IsAlgClosed k] [CharP k 2] in
private theorem matrixRankOne_eq_matrixN (r : Root) (t : kˣ) :
    matrixRankOne r t = matrixN (F := k) r t := by
  simp only [matrixRankOne, matrixN, Units.val_inv_eq_inv_val]

omit [CharP k 2] in
private theorem matrixRankOne_simple_mem (i : typeF4RootPairing_base.support) (t : kˣ) :
    matrixRankOne i.val t ∈ matrixTits (k := k) ⊔ matrixTorus := by
  have he : matrixRankOne i.val t = diag i t⁻¹ * titsUnit [i] := by
    have h := matrixH_simple (F := k) i t
    rw [matrixH, matrixN_neg_one, matrixN_one] at h
    rw [← matrixRankOne_eq_matrixN] at h
    change matrixRankOne i.val t * (titsUnit [i])⁻¹ = diag i t⁻¹ at h
    calc
      _ = (matrixRankOne i.val t * (titsUnit [i])⁻¹) * titsUnit [i] := by group
      _ = _ := by rw [h]
  rw [he]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (diag_mem i t⁻¹))
    (Subgroup.mem_sup_left (word_mem_matrixTits [i]))

private theorem matrixRankOne_neg_simple_mem (i : typeF4RootPairing_base.support) (t : kˣ) :
    matrixRankOne (-i.val) t ∈ matrixTits (k := k) ⊔ matrixTorus := by
  have hp (a : k) : titsUnit [i] * rootCurve i.val a * (titsUnit [i])⁻¹ =
      rootCurve (-i.val) a := simple_conj i i.val a
  have hn (a : k) : titsUnit [i] * rootCurve (-i.val) a * (titsUnit [i])⁻¹ =
      rootCurve (-(-i.val)) a := by
    rw [neg_neg]
    simpa only [RootPairing.indexNeg_neg, RootPairing.reflectionPerm_self] using
      simple_conj i (-i.val) a
  rw [matrixRankOne_conjugate (titsUnit [i]) i.val (-i.val) hp hn t]
  have hw : titsUnit (S := k) [i] ∈ matrixTits (k := k) ⊔ matrixTorus :=
    Subgroup.mem_sup_left (word_mem_matrixTits [i])
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (matrixRankOne_simple_mem i t))
    (Subgroup.inv_mem _ hw)

private theorem matrixRankOne_mem_sup (r : Root) (t : kˣ) :
    matrixRankOne r t ∈ matrixTits (k := k) ⊔ matrixTorus := by
  by_cases hr : typeF4RootPairing_base.IsPos r
  · let D := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
    have hp (a : k) : titsUnit D.word * rootCurve D.simple.val a *
        (titsUnit D.word)⁻¹ = rootCurve r a := (rootCurve_of_pos_route r hr a).symm
    have hn (a : k) : titsUnit D.word * rootCurve (-D.simple.val) a *
        (titsUnit D.word)⁻¹ = rootCurve (-r) a := (rootCurve_neg_of_pos_route r hr a).symm
    rw [matrixRankOne_conjugate (titsUnit D.word) D.simple.val r hp hn t]
    have hw : titsUnit (S := k) D.word ∈ matrixTits (k := k) ⊔ matrixTorus :=
      Subgroup.mem_sup_left (word_mem_matrixTits D.word)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (matrixRankOne_simple_mem D.simple t))
      (Subgroup.inv_mem _ hw)
  · have hneg := (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr
    let D := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)
    have hp (a : k) : titsUnit D.word * rootCurve (-D.simple.val) a *
        (titsUnit D.word)⁻¹ = rootCurve r a := by
      simpa only [neg_neg] using (rootCurve_neg_of_pos_route (-r) hneg a).symm
    have hn (a : k) : titsUnit D.word * rootCurve (-(-D.simple.val)) a *
        (titsUnit D.word)⁻¹ = rootCurve (-r) a := by
      simpa only [neg_neg] using (rootCurve_of_pos_route (-r) hneg a).symm
    rw [matrixRankOne_conjugate (titsUnit D.word) (-D.simple.val) r hp hn t]
    have hw : titsUnit (S := k) D.word ∈ matrixTits (k := k) ⊔ matrixTorus :=
      Subgroup.mem_sup_left (word_mem_matrixTits D.word)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (matrixRankOne_neg_simple_mem D.simple t))
      (Subgroup.inv_mem _ hw)
omit [CharP k 2] in
theorem literalMatrix_ambient (x : Variety.Point (Carrier (k := k))) :
    matrixAmbientEquiv (literalMatrix x) = (ambientClosedCarrier (k := k)).inclusion.onPoints x := by
  simp only [literalMatrix, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]

omit [CharP k 2] in
private theorem exists_coroot_matrix (u : typeF4RootPairing_base.support → kˣ) :
    ∃ t : Fin 4 → kˣ, literalMatrix (corootProduct t) = torusMatrixHom u := by
  refine ⟨(u ∘ typeF4RootPairing_baseEquiv)⁻¹, ?_⟩
  apply matrixAmbientEquiv.injective
  rw [literalMatrix_ambient, corootProduct_ambient, inv_inv]
  apply congrArg matrixToAmbient
  change integralChevalleyTorusElement (P := typeF4RootPairing)
    (torusParameter (u ∘ typeF4RootPairing_baseEquiv)) =
      integralChevalleyTorusElement (P := typeF4RootPairing) u
  congr 1
  funext i
  simp only [torusParameter, Function.comp_apply, Equiv.apply_symm_apply]

private theorem simpleN_inv (i : Fin 4) :
    (algebraicNElement (typeF4SimpleRootIndex i) (1 : kˣ))⁻¹ =
      algebraicNElement (typeF4SimpleRootIndex i) 1 := by
  apply literalMatrix_injective
  rw [map_inv, literalMatrix_simpleN, simple_lift_inv]

omit [CharP k 2] in
theorem weylWord_append (l m : List (Fin 4)) :
    weylWord (F := k) (l ++ m) = weylWord l * weylWord m := by
  simp only [weylWord, List.map_append, List.prod_append]

theorem weylWord_reverse (l : List (Fin 4)) :
    weylWord (F := k) l.reverse = (weylWord l)⁻¹ := by
  induction l with
  | nil => simp [weylWord]
  | cons i l ih =>
    rw [List.reverse_cons, weylWord_append, ih]
    simp only [weylWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_inv_rev, simpleN_inv]

private theorem matrixTits_exists_word (a : MatrixUnit k) (ha : a ∈ matrixTits (k := k)) :
    ∃ l : List (Fin 4), literalMatrix (weylWord (F := k) l) = a := by
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    refine ⟨[typeF4RootPairing_baseEquiv.symm i], ?_⟩
    simp only [weylWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, literalMatrix_simpleN, Equiv.apply_symm_apply]
  | one => exact ⟨[], by simp [weylWord]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨l, rfl⟩ := ha
    obtain ⟨m, rfl⟩ := hb
    exact ⟨l ++ m, by rw [weylWord_append, map_mul]⟩
  | inv a _ ha =>
    obtain ⟨l, rfl⟩ := ha
    exact ⟨l.reverse, by rw [weylWord_reverse, map_inv]⟩

/-- Normalizer coverage with actual simple parameter-one list products and
literal direct coroot parameters, rather than abstract coset representatives. -/
theorem normalizerWords_eq_corootProduct_mul_weylWord
    {n : Variety.Point (Carrier (k := k))} (hn : n ∈ normalizerWords (k := k)) :
    ∃ (t : Fin 4 → kˣ) (l : List (Fin 4)), n = corootProduct t * weylWord l := by
  have hm : literalMatrix n ∈ matrixTits (k := k) ⊔ matrixTorus := by
    have hle : normalizerWords (k := k) ≤
        (matrixTits (k := k) ⊔ matrixTorus).comap literalMatrix := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨r, t, rfl⟩
      change literalMatrix (rankOne r t) ∈ (matrixTits (k := k) ⊔ matrixTorus)
      rw [literalMatrix_rankOne]
      exact matrixRankOne_mem_sup r t
    exact hle hn
  have hm' : literalMatrix n ∈
      (matrixTorus (k := k) : Set (MatrixUnit k)) * (matrixTits (k := k) : Set (MatrixUnit k)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ matrixTits_le_normalizer, sup_comm]
    exact hm
  obtain ⟨a, ⟨u, rfl⟩, b, hb, hab⟩ := hm'
  obtain ⟨l, hl⟩ := matrixTits_exists_word b hb
  obtain ⟨t, ht⟩ := exists_coroot_matrix u
  refine ⟨t, l, literalMatrix_injective ?_⟩
  rw [map_mul, ht, hl]
  exact hab.symm

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.RestrictedCells
