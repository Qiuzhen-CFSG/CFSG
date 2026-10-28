module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ZeroAndMiddle.Geometry
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SplitTorus
public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.SimpleConjugation

/-!
# Literal opposite-root transport in the F4 carrier

Every positive root curve and its negative are transported simultaneously from
one simple pair by the same chosen integral Tits word. The word is realized as
an actual point of the closed F4 carrier. Its simple factors preserve the literal
split torus: the four simple coroots generate that torus, and their checked
commutation law gives invariance. For a negative target, append the simple Tits
representative, which exchanges the simple pair in characteristic two.

This supplies the transport input for the literal rank-one chart construction
without assuming a chart or a root-subgroup uniqueness theorem.

Source: GLS3, Theorem 1.9.5(c,d,f) and the defining root words of Theorem 1.12.1,
`refs/KGroup/GLS3/Chapter1.tex`; the integral Tits construction follows Steinberg,
*Lectures on Chevalley Groups*.
-/

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4.BinaryDegree.ExceptionalTensor
namespace Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
noncomputable section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
local instance : InvolutiveNeg Root := typeF4RootPairing.indexNeg

/-- The four literal simple-coroot families generate all points of the split torus. -/
private lemma splitTorus_le_of_coroot_mem
    (H : Subgroup (Variety.Point (Carrier (k := k))))
    (hH : ∀ (i : Fin 4) (t : kˣ), algebraicCorootElement (typeF4SimpleRootIndex i) t ∈ H) :
    (splitTorus (k := k)).toSubgroup ≤ H := by
  classical
  let f := (ambientClosedCarrier (k := k)).inclusion.onPoints
  let K := (H.map f).comap (matrixToAmbient.comp torusMatrixHom)
  have hs (i : typeF4RootPairing_base.support) (t : kˣ) :
      integralChevalleySimpleCorootParameter i t ∈ K := by
    obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
    refine ⟨algebraicCorootElement (typeF4SimpleRootIndex j) t⁻¹, hH j t⁻¹, ?_⟩
    change (ambientClosedCarrier (k := k)).inclusion.onPoints _ = _
    rw [algebraicCorootElement_ambient, matrixH_simple]
    simp only [inv_inv]
    rfl
  have hall (u : typeF4RootPairing_base.support → kˣ) : u ∈ K := by
    have hu : u = ∏ i, integralChevalleySimpleCorootParameter i (u i) := by
      funext j
      simp [integralChevalleySimpleCorootParameter, Finset.prod_apply]
    rw [hu]
    exact K.prod_mem (fun i _ => hs i (u i))
  rintro x ⟨z, rfl⟩
  have hz : f (splitTorusMorphism.onPoints z) ∈ H.map f := by
    change (ambientClosedCarrier (k := k)).inclusion.onPoints _ ∈ H.map f
    rw [splitTorusMorphism_inclusion_apply, torusAmbientMorphism_matrix]
    exact hall (torusParameter (dPointEquiv 4 z))
  obtain ⟨y, hy, he⟩ := hz
  exact (ambientClosedCarrier (k := k)).inclusion_injective he ▸ hy

variable [CharP k 2]

private lemma simpleN_inv (i : typeF4RootPairing_base.support) :
    (algebraicNElement (F := k) i 1)⁻¹ = algebraicNElement i 1 := by
  simp only [algebraicNElement, mul_inv_rev, ZeroAndMiddle.root_inv, CharTwo.neg_eq]
  group

private lemma simpleN_torus (i : typeF4RootPairing_base.support) :
    (splitTorus (k := k)).conjugate (algebraicNElement i 1) = splitTorus := by
  obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
  let n := algebraicNElement (F := k) (typeF4SimpleRootIndex j) 1
  have hle : (splitTorus (k := k)).toSubgroup ≤
      (splitTorus (k := k)).toSubgroup.comap (MulAut.conj n⁻¹).toMonoidHom := by
    apply splitTorus_le_of_coroot_mem
    intro q t
    change n⁻¹ * algebraicCorootElement (typeF4SimpleRootIndex q) t * (n⁻¹)⁻¹ ∈ splitTorus
    rw [inv_inv]
    have he := ZeroAndMiddle.coroot_n_commute (F := k) j q t
    have hc : n⁻¹ * algebraicCorootElement (typeF4SimpleRootIndex q) t * n =
        algebraicCorootElement (typeF4SimpleRootIndex q) t *
          algebraicCorootElement (typeF4SimpleRootIndex j) (t ^ (-typeF4CartanMatrix j q)) := by
      rw [mul_assoc]
      rw [he]
      change n⁻¹ * (n * _) = _
      exact inv_mul_cancel_left _ _
    rw [hc]
    exact Subgroup.mul_mem _ (algebraicCorootElement_mem_splitTorus q t)
      (algebraicCorootElement_mem_splitTorus j _)
  have hc (x : Variety.Point (Carrier (k := k))) (hx : x ∈ splitTorus (k := k)) :
      n⁻¹ * x * n ∈ splitTorus (k := k) := by
    have hh := hle hx
    change n⁻¹ * x * (n⁻¹)⁻¹ ∈ splitTorus at hh
    simpa only [inv_inv] using hh
  apply SetLike.coe_injective
  ext x
  change x ∈ (splitTorus (k := k)).conjugate n ↔ x ∈ splitTorus
  rw [ClosedSubgroup.mem_conjugate_iff]
  constructor
  · intro hx
    have hh := hc _ hx
    have hn : n⁻¹ = n := simpleN_inv (typeF4RootPairing_baseEquiv j)
    have he : n⁻¹ * (n⁻¹ * x * n) * n = x := by
      calc
        _ = n * (n⁻¹ * x * n) * n⁻¹ := by rw [hn]
        _ = x := by group
    rwa [he] at hh
  · exact hc x

/-- Realization of the chosen integral word in the actual closed carrier. -/
private def titsPoint : List typeF4RootPairing_base.support → Variety.Point (Carrier (k := k))
  | [] => 1
  | i :: w => algebraicNElement i 1 * titsPoint w

omit [CharP k 2] in
private lemma titsPoint_matrix (w : List typeF4RootPairing_base.support) :
    ZeroAndMiddle.carrierMatrix (titsPoint (k := k) w) = rootCurveTitsWord w := by
  induction w with
  | nil => simp [titsPoint]
  | cons i w ih =>
    simp only [titsPoint, map_mul, ZeroAndMiddle.carrierMatrix_n, ih]
    simp only [Units.val_one]
    rw [ZeroAndMiddle.matrixN_one, rootCurveTitsWord_cons, rootCurveTitsWord_cons,
      rootCurveTitsWord_nil, mul_one]

private lemma titsPoint_torus (w : List typeF4RootPairing_base.support) :
    (splitTorus (k := k)).conjugate (titsPoint w) = splitTorus := by
  induction w with
  | nil => exact ClosedSubgroup.conjugate_one _
  | cons i w ih =>
    change (splitTorus (k := k)).conjugate (algebraicNElement i 1 * titsPoint w) = _
    rw [← ClosedSubgroup.conjugate_conjugate, ih, simpleN_torus]

omit [CharP k 2] in
private lemma rootSubgroup_conjugate_of_elements (a b : Root)
    (g : Variety.Point (Carrier (k := k)))
    (h : ∀ t : k, g * algebraicRootElement a t * g⁻¹ = algebraicRootElement b t) :
    (rootSubgroup (k := k) a).conjugate g = rootSubgroup b := by
  have hmem (r : Root) (x : Variety.Point (Carrier (k := k))) :
      x ∈ rootSubgroup r ↔ ∃ t : k, algebraicRootElement r t = x := by
    constructor
    · rintro ⟨q, rfl⟩
      refine ⟨q.val PUnit.unit, ?_⟩
      have hq : kPlusPoint (q.val PUnit.unit) = q := by
        apply (additiveGroupPointEquiv k).injective
        rfl
      exact congrArg (rootMorphism r).onPoints hq
    · rintro ⟨t, rfl⟩
      exact ⟨kPlusPoint t, rfl⟩
  apply SetLike.coe_injective
  ext x
  change x ∈ (rootSubgroup (k := k) a).conjugate g ↔ x ∈ rootSubgroup b
  rw [ClosedSubgroup.mem_conjugate_iff]
  change g⁻¹ * x * g ∈ rootSubgroup a ↔ x ∈ rootSubgroup b
  rw [hmem, hmem]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← h, ht]
    group
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    rw [← h]
    group

private lemma positive_pair (r : Root) (hr : typeF4RootPairing_base.IsPos r) :
    ∃ i : typeF4RootPairing_base.support, ∃ g : Variety.Point (Carrier (k := k)),
      (splitTorus (k := k)).conjugate g = splitTorus ∧
      (rootSubgroup (k := k) i).conjugate g = rootSubgroup r ∧
      (rootSubgroup (k := k) (-i : Root)).conjugate g = rootSubgroup (-r) := by
  let route := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  refine ⟨route.simple, titsPoint route.word, titsPoint_torus _, ?_, ?_⟩
  · apply rootSubgroup_conjugate_of_elements
    intro t
    apply ZeroAndMiddle.carrierMatrix_injective
    simp only [map_mul, map_inv, ZeroAndMiddle.carrierMatrix_root, titsPoint_matrix]
    change _ = rootCurveUnit
      (integralChevalleyRootOperators (P := typeF4RootPairing) (b := typeF4RootPairing_base)) r t
    rw [rootCurveUnit_of_pos r hr]
    change _ * rootCurveUnit
      (integralChevalleyRootOperators (P := typeF4RootPairing) (b := typeF4RootPairing_base)) route.simple t * _ = _
    rw [rootCurveUnit_simple]
  · apply rootSubgroup_conjugate_of_elements
    intro t
    apply ZeroAndMiddle.carrierMatrix_injective
    simp only [map_mul, map_inv, ZeroAndMiddle.carrierMatrix_root, titsPoint_matrix]
    have hn : ¬ typeF4RootPairing_base.IsPos (-r) := by
      rw [RootPairing.Base.IsPos.neg_iff_not]
      exact not_not.mpr hr
    change _ = rootCurveUnit
      (integralChevalleyRootOperators (P := typeF4RootPairing) (b := typeF4RootPairing_base)) (-r) t
    rw [rootCurveUnit_of_neg (-r) hn, neg_neg]
    change _ * rootCurveUnit
      (integralChevalleyRootOperators (P := typeF4RootPairing) (b := typeF4RootPairing_base)) (-route.simple : Root) t * _ = _
    rw [rootCurveUnit_neg_simple]

private lemma simple_pair_swap (i : typeF4RootPairing_base.support) :
    (rootSubgroup (k := k) i).conjugate (algebraicNElement i 1) = rootSubgroup (-i : Root) ∧
    (rootSubgroup (k := k) (-i : Root)).conjugate (algebraicNElement i 1) = rootSubgroup i := by
  have hp : (rootSubgroup (k := k) i).conjugate (algebraicNElement i 1) =
      rootSubgroup (-i : Root) := by
    apply rootSubgroup_conjugate_of_elements
    intro t
    apply ZeroAndMiddle.carrierMatrix_injective
    simp only [map_mul, map_inv, ZeroAndMiddle.carrierMatrix_root, ZeroAndMiddle.carrierMatrix_n]
    have he := ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.simple_conj
      (S := k) i i t
    simp only [Units.val_one, ZeroAndMiddle.matrixN_one]
    exact he
  refine ⟨hp, ?_⟩
  have hnn : algebraicNElement (F := k) i 1 * algebraicNElement i 1 = 1 := by
    calc
      _ = (algebraicNElement (F := k) i 1)⁻¹ * algebraicNElement i 1 := by rw [simpleN_inv]
      _ = 1 := inv_mul_cancel _
  rw [← hp, ClosedSubgroup.conjugate_conjugate, hnn, ClosedSubgroup.conjugate_one]

/-- Every literal opposite-root pair is the simultaneous conjugate of a simple
pair by one point preserving the literal split torus. -/
public theorem literalRootPairTransport (r : Root) :
    ∃ (i : typeF4RootPairing_base.support) (g : Variety.Point (Carrier (k := k))),
      (splitTorus (k := k)).conjugate g = splitTorus ∧
      (rootSubgroup (k := k) i).conjugate g = rootSubgroup r ∧
      (rootSubgroup (k := k) (typeF4RootPairing.reflectionPerm i i)).conjugate g =
        rootSubgroup (typeF4RootPairing.reflectionPerm r r) := by
  change ∃ (i : typeF4RootPairing_base.support) (g : Variety.Point (Carrier (k := k))),
    (splitTorus (k := k)).conjugate g = splitTorus ∧
    (rootSubgroup (k := k) i).conjugate g = rootSubgroup r ∧
    (rootSubgroup (k := k) (-i : Root)).conjugate g = rootSubgroup (-r)
  by_cases hr : typeF4RootPairing_base.IsPos r
  · exact positive_pair r hr
  · have hn : typeF4RootPairing_base.IsPos (-r) :=
      (RootPairing.Base.IsPos.neg_iff_not _ _).mpr hr
    obtain ⟨i, g, hT, hp, hm⟩ := positive_pair (k := k) (-r) hn
    rw [neg_neg] at hm
    refine ⟨i, g * algebraicNElement i 1, ?_, ?_, ?_⟩
    · rw [← ClosedSubgroup.conjugate_conjugate, simpleN_torus, hT]
    · rw [← ClosedSubgroup.conjugate_conjugate, (simple_pair_swap i).1, hm]
    · rw [← ClosedSubgroup.conjugate_conjugate, (simple_pair_swap i).2, hp]

end
end Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
