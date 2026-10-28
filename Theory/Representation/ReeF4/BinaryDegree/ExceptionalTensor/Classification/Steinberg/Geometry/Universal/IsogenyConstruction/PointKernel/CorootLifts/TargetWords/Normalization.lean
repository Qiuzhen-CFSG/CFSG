module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.RankOne
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Coroots
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.AlgebraicGroup.RootSubgroups.RootCocharacterChoice
public import Theory.AlgebraicGroup.RootSubgroups.Conjugation
public import Theory.AlgebraicGroup.Tori.Character.FiniteGeneration
public import Theory.AlgebraicGroup.Tori.Power
public import Mathlib.LinearAlgebra.Reflection

/-!
# Cartan normalization of actual rank-one charts

A compatible SL₂ chart on two opposite actual root subgroups determines the
source word `n(1)⁻¹n(t)`. Its diagonal matrix `diag(t⁻¹,t)` first gives exponent
two on its own root. Conjugating the Weyl word by an arbitrary torus point
then yields the commutator identity `n⁻¹s⁻¹ns = h(α(s))`. In characteristic two,
`n` is an involution, so it normalizes the torus and acts on its characters
by `β ↦ β α⁻ᵐ`, where `m` is evaluation of β on the chart cocharacter.

Conjugation preserves actual torus roots. The chart's reflection and the
realization's reflection therefore preserve the same finite set of characters.
Uniqueness of reflection functionals on the span of a finite set identifies
all the exponents with the Cartan integers. The F4 specialization uses the
actual root-index equivalence only to obtain finiteness; it is independent of
the model's chosen positive base.

Sources: GLS3, Theorem 1.9.5(c)--(d), Remarks 1.9.6 and Theorem 1.12.1(g),
with the defining formula preceding it, `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem
universe u
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

private lemma binarySL2Coroot_upper (t : Variety.Point (KMult k)) (s : k) :
    (binarySL2Coroot.onPoints t)⁻¹ *
      standardSL2UpperMorphism.onPoints (kPlusPoint s) * binarySL2Coroot.onPoints t =
        standardSL2UpperMorphism.onPoints
          (kPlusPoint ((dPointEquiv 1 t 0 : k) ^ (2 : ℤ) * s)) := by
  apply (mul_left_cancel_iff (a := binarySL2Coroot.onPoints t)).mp
  simp only [← mul_assoc, mul_inv_cancel, one_mul]
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change slPointMatrix 2 (standardSL2UpperMorphism.onPoints (kPlusPoint s) *
      binarySL2Coroot.onPoints t) = slPointMatrix 2 (binarySL2Coroot.onPoints t * _)
  have hmul (x y : Variety.Point (slVariety k 2)) :
      slPointMatrix 2 (x * y) = slPointMatrix 2 x * slPointMatrix 2 y := rfl
  rw [hmul, hmul, binarySL2Coroot_matrix]
  have hu (c : k) : slPointMatrix 2 (standardSL2UpperMorphism.onPoints (kPlusPoint c)) =
      Matrix.transvection (0 : Fin 2) 1 c := rfl
  rw [hu, hu]
  have ht : (dPointEquiv 1 t 0 : k) ≠ 0 := (dPointEquiv 1 t 0).ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply, Matrix.diagonal]
  field_simp

namespace BinaryOppositeRootSL2Chart
variable {G : Variety k} [AlgebraicGroup G] {T X Y : ClosedSubgroup G}
variable (C : BinaryOppositeRootSL2Chart T X Y)

private lemma map_upper (s : k) :
    (oppositePairGeneratedSubgroup X Y).inclusion.onPoints
      (C.map.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint s))) =
        X.inclusion.onPoints (C.plus.value s) := by
  have h := congrArg (fun f : Morphism (KPlus k)
    (oppositePairGeneratedSubgroup X Y).carrierVariety => f.onPoints (kPlusPoint s))
      C.compatible.1
  change (oppositePairPlusMorphism X Y).onPoints (C.plus.value s) =
    C.map.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint s)) at h
  rw [← h]
  exact oppositePairPlusMorphism_inclusion_apply X Y (C.plus.value s)

/-- A chart has the source exponent two on its upper root. -/
theorem self_weight (χ : TorusWeight T) (hχ : RootWeightEquation T X χ) :
    WeightCocharacterEquation T χ C.cocharacter 2 := by
  intro t
  have h := congrArg (fun z => (oppositePairGeneratedSubgroup X Y).inclusion.onPoints
    (C.map.onPoints z)) (binarySL2Coroot_upper t (1 : k))
  simp only [map_mul, map_inv, C.map_upper, ← C.cocharacter_inclusion_apply] at h
  have hw := hχ C.plus 1 (C.cocharacter.onPoints t)
  change (T.inclusion.onPoints _)⁻¹ * X.inclusion.onPoints (C.plus.value 1) *
    T.inclusion.onPoints _ = X.inclusion.onPoints (C.plus.value _) at hw
  have hp := X.inclusion_injective (hw.symm.trans h)
  have hq := C.plus.toMulEquiv.injective hp
  have hv := congrArg (fun z : Variety.Point (KPlus k) => z.val PUnit.unit) hq
  change χ.pointCharacter (C.cocharacter.onPoints t) * 1 =
    (dPointEquiv 1 t 0 : k) ^ (2 : ℤ) * 1 at hv
  simpa only [mul_one] using hv

/-- The actual source-convention Weyl word at parameter one. -/
noncomputable def weyl : Variety.Point G :=
  X.inclusion.onPoints (C.plus.value 1) * Y.inclusion.onPoints (C.minus.value 1) *
    X.inclusion.onPoints (C.plus.value 1)

/-- The opaque Weyl point is the literal product of its two root factors.
This identity allows membership in a subgroup to be proved from the actual
root subgroup inclusions without exposing the definition body. -/
theorem weyl_eq : C.weyl =
    X.inclusion.onPoints (C.plus.value 1) * Y.inclusion.onPoints (C.minus.value 1) *
      X.inclusion.onPoints (C.plus.value 1) := by
  unfold weyl
  rfl

omit [IsAlgClosed k] in
private lemma value_one_inv {H : Variety k} [AlgebraicGroup H]
    (x : OneParameterParametrization H) : (x.value 1)⁻¹ = x.value 1 := by
  have h : (kPlusPoint (1 : k))⁻¹ = kPlusPoint (1 : k) := by
    apply (additiveGroupPointEquiv k).injective
    change Multiplicative.ofAdd (-(1 : k)) = Multiplicative.ofAdd 1
    rw [CharTwo.neg_eq]
  change (x.hom.onPoints (kPlusPoint 1))⁻¹ = _
  rw [← map_inv, h]
  rfl

/-- In characteristic two the Weyl word is an involution. -/
theorem weyl_inv : C.weyl⁻¹ = C.weyl := by
  simp only [weyl, mul_inv_rev, ← map_inv, value_one_inv]
  group

/-- Conjugating the Weyl word by a torus point produces its coroot word. -/
theorem weyl_commutator (χ : TorusWeight T)
    (hχ : RootWeightEquation T X χ) (hχneg : RootWeightEquation T Y χ⁻¹)
    (s : Variety.Point T.carrierVariety) :
    C.weyl⁻¹ * (T.inclusion.onPoints s)⁻¹ * C.weyl * T.inclusion.onPoints s =
      T.inclusion.onPoints (C.cocharacter.onPoints (χ.onPoints s)) := by
  rw [← C.word_eq_cocharacter, binaryCorootWord_apply]
  change C.weyl⁻¹ * (T.inclusion.onPoints s)⁻¹ * C.weyl * T.inclusion.onPoints s =
    C.weyl⁻¹ * (X.inclusion.onPoints (C.plus.value (χ.pointCharacter s)) *
      Y.inclusion.onPoints (C.minus.value ((χ.pointCharacter s)⁻¹)) *
      X.inclusion.onPoints (C.plus.value (χ.pointCharacter s)))
  have heval (ψ : TorusWeight T) : ψ.pointCharacter s =
      (torusPointEval T.carrierVariety s ψ : k) := rfl
  have hinv : (χ⁻¹).pointCharacter s = (χ.pointCharacter s)⁻¹ := by
    rw [heval, heval]
    exact (congrArg Units.val ((torusPointEval T.carrierVariety s).map_inv χ)).trans
      (Units.val_inv_eq_inv_val _)
  have hp := hχ C.plus 1 s
  have hm := hχneg C.minus 1 s
  simp only [mul_one, hinv] at hp hm
  change (T.inclusion.onPoints s)⁻¹ * X.inclusion.onPoints (C.plus.value 1) *
    T.inclusion.onPoints s = X.inclusion.onPoints
      (C.plus.value (χ.pointCharacter s)) at hp
  change (T.inclusion.onPoints s)⁻¹ * Y.inclusion.onPoints (C.minus.value 1) *
    T.inclusion.onPoints s = Y.inclusion.onPoints
      (C.minus.value ((χ.pointCharacter s)⁻¹)) at hm
  rw [← hp, ← hm]
  dsimp [weyl]
  group

/-- The Weyl word acts on the torus by the rank-one reflection formula. -/
theorem weyl_conjugation (χ : TorusWeight T)
    (hχ : RootWeightEquation T X χ) (hχneg : RootWeightEquation T Y χ⁻¹)
    (s : Variety.Point T.carrierVariety) :
    C.weyl * T.inclusion.onPoints s * C.weyl⁻¹ =
      T.inclusion.onPoints (s * (C.cocharacter.onPoints (χ.onPoints s))⁻¹) := by
  have h := C.weyl_commutator χ hχ hχneg s
  rw [map_mul, map_inv]
  calc
    _ = C.weyl⁻¹ * T.inclusion.onPoints s * C.weyl := by rw [C.weyl_inv]
    _ = T.inclusion.onPoints s *
        (C.weyl⁻¹ * (T.inclusion.onPoints s)⁻¹ * C.weyl * T.inclusion.onPoints s)⁻¹ := by
          group
    _ = _ := by rw [h]

/-- The chart Weyl word normalizes the actual torus. -/
theorem weyl_mem_normalizer (χ : TorusWeight T)
    (hχ : RootWeightEquation T X χ) (hχneg : RootWeightEquation T Y χ⁻¹) :
    C.weyl ∈ T.normalizer.toSubgroup := by
  have hf (x : Variety.Point G) (hx : x ∈ T) : C.weyl * x * C.weyl⁻¹ ∈ T := by
    obtain ⟨s, rfl⟩ : ∃ s, T.inclusion.onPoints s = x := by
      rw [← Set.mem_range, T.range_inclusion]
      exact hx
    rw [C.weyl_conjugation χ hχ hχneg]
    exact (T.pointEquiv _).property
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  refine ⟨hf x, ?_⟩
  intro hx
  have hh := hf _ hx
  have heq : C.weyl * (C.weyl * x * C.weyl⁻¹) * C.weyl⁻¹ = x := by
    calc
      _ = C.weyl⁻¹ * (C.weyl * x * C.weyl⁻¹) * C.weyl := by rw [C.weyl_inv]
      _ = x := by group
  rwa [heq] at hh

/-- Conjugation by the chart Weyl word reflects every actual root weight.
The exponent here is evaluation on the constructed cocharacter, not an
assumed Cartan integer. -/
theorem reflected_isTorusRoot (α β : TorusWeight T)
    (hα : RootWeightEquation T X α) (hαneg : RootWeightEquation T Y α⁻¹)
    (hβ : IsTorusRoot T β) :
    IsTorusRoot T (β * α ^ (-characterCocharacterPairing T C.cocharacter (Additive.ofMul β))) := by
  obtain ⟨Z, hZ, hβ⟩ := hβ
  refine ⟨Z.conjugate C.weyl,
    hZ.conjugate_of_mem_normalizer C.weyl (C.weyl_mem_normalizer α hα hαneg), ?_⟩
  intro x a s
  let e := Z.conjugateIso C.weyl
  let y : OneParameterParametrization Z.carrierVariety := e.symm.comp x
  let s₀ := s * (C.cocharacter.onPoints (α.onPoints s))⁻¹
  have hs : T.inclusion.onPoints s₀ =
      C.weyl⁻¹ * T.inclusion.onPoints s * C.weyl := by
    dsimp [s₀]
    rw [← C.weyl_conjugation α hα hαneg, C.weyl_inv]
  have hy (c : k) : Z.inclusion.onPoints (y.value c) =
      C.weyl⁻¹ * (Z.conjugate C.weyl).inclusion.onPoints (x.value c) * C.weyl :=
    Z.conjugateIso_inv_inclusion_apply C.weyl (x.value c)
  have hv : β.pointCharacter s₀ =
      (β * α ^ (-characterCocharacterPairing T C.cocharacter (Additive.ofMul β))).pointCharacter s := by
    dsimp [s₀]
    rw [map_mul, map_inv, characterCocharacterPairing_spec]
    change β.pointCharacter s * ((α.pointCharacter s) ^
      characterCocharacterPairing T C.cocharacter (Additive.ofMul β))⁻¹ = _
    have h := congrArg Units.val ((torusPointEval T.carrierVariety s).map_mul β
      (α ^ (-characterCocharacterPairing T C.cocharacter (Additive.ofMul β))))
    rw [map_zpow] at h
    have heval (ψ : TorusWeight T) : ψ.pointCharacter s =
        (torusPointEval T.carrierVariety s ψ : k) := rfl
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val] at h
    rw [heval, heval, heval]
    simpa only [zpow_neg] using h.symm
  have h := hβ y a s₀
  change (T.inclusion.onPoints s₀)⁻¹ * Z.inclusion.onPoints (y.value a) *
    T.inclusion.onPoints s₀ = Z.inclusion.onPoints (y.value (β.pointCharacter s₀ * a)) at h
  rw [hs, hy, hv, hy] at h
  change (T.inclusion.onPoints s)⁻¹ * (Z.conjugate C.weyl).inclusion.onPoints (x.value a) *
    T.inclusion.onPoints s = (Z.conjugate C.weyl).inclusion.onPoints (x.value _)
  apply (MulAut.conj C.weyl⁻¹).injective
  simp only [MulAut.conj_apply, inv_inv]
  calc
    _ = (C.weyl⁻¹ * T.inclusion.onPoints s * C.weyl)⁻¹ *
        (C.weyl⁻¹ * (Z.conjugate C.weyl).inclusion.onPoints (x.value a) * C.weyl) *
        (C.weyl⁻¹ * T.inclusion.onPoints s * C.weyl) := by group
    _ = _ := h

end BinaryOppositeRootSL2Chart

namespace RootGroupData
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
variable (D : RootGroupData G T)

/-- A compatible rank-one chart realizes the Cartan pairing on every root.
Finiteness of the root system makes its reflection functional unique. -/
theorem chart_isCartan [Finite D.Root] (hD : D.IsRealization) (hT : IsTorus T.carrierVariety)
    (a : D.Root) (C : BinaryOppositeRootSL2Chart T (D.rootSubgroup a)
      (D.rootSubgroup (D.neg a))) :
    D.IsCartanRootCocharacter a C.cocharacter := by
  let : IsMulTorsionFree (TorusWeight T) :=
    torusCharacter_isTorsionFree_of_isConnected T.carrierVariety hT.isConnected
  let roots : Set (Additive (TorusWeight T)) := Set.range (fun b => Additive.ofMul (D.rootWeight b))
  let f := (characterCocharacterPairing T C.cocharacter).toIntLinearMap
  let g := (D.characterCorootPairing a).toIntLinearMap
  have ha : RootWeightEquation T (D.rootSubgroup a) (D.rootWeight a) := (hD.2.2.1 a).2
  have hneg : RootWeightEquation T (D.rootSubgroup (D.neg a)) (D.rootWeight a)⁻¹ := by
    rw [← hD.2.2.2.1 a]
    exact (hD.2.2.1 (D.neg a)).2
  have hf : f (Additive.ofMul (D.rootWeight a)) = 2 :=
    (weightCocharacterEquation_existsUnique T (D.rootWeight a) C.cocharacter).unique
      (characterCocharacterPairing_spec T (D.rootWeight a) C.cocharacter)
      (C.self_weight (D.rootWeight a) ha)
  have hg : g (Additive.ofMul (D.rootWeight a)) = 2 := by
    change D.characterCorootPairing a (Additive.ofMul (D.rootWeight a)) = 2
    rw [hD.characterCorootPairing_rootWeight, hD.2.2.2.2.2.2.1 a]
  have heq (q : Additive (TorusWeight T) →ₗ[ℤ] ℤ) (b : D.Root) :
      Module.preReflection (Additive.ofMul (D.rootWeight a)) q
        (Additive.ofMul (D.rootWeight b)) =
          Additive.ofMul (D.rootWeight b * D.rootWeight a ^ (-q (Additive.ofMul (D.rootWeight b)))) := by
    change Additive.ofMul (D.rootWeight b / D.rootWeight a ^ q (Additive.ofMul (D.rootWeight b))) = _
    rw [div_eq_mul_inv, zpow_neg]
  have hfroot : Set.MapsTo (Module.preReflection (Additive.ofMul (D.rootWeight a)) f) roots roots := by
    rintro _ ⟨b, rfl⟩
    rw [heq]
    have hb := C.reflected_isTorusRoot (D.rootWeight a) (D.rootWeight b) ha hneg
      ⟨D.rootSubgroup b, hD.2.2.1 b⟩
    have hb' : D.rootWeight b * D.rootWeight a ^
        (-characterCocharacterPairing T C.cocharacter (Additive.ofMul (D.rootWeight b))) ∈
          Set.range D.rootWeight := by
      rw [hD.2.1]
      exact hb
    obtain ⟨c, hc⟩ := hb'
    exact ⟨c, congrArg Additive.ofMul hc⟩
  have hgroot : Set.MapsTo (Module.preReflection (Additive.ofMul (D.rootWeight a)) g) roots roots := by
    rintro _ ⟨b, rfl⟩
    rw [heq]
    refine ⟨D.reflect a b, ?_⟩
    change Additive.ofMul (D.rootWeight (D.reflect a b)) =
      Additive.ofMul (D.rootWeight b * D.rootWeight a ^
        (-D.characterCorootPairing a (Additive.ofMul (D.rootWeight b))))
    rw [hD.characterCorootPairing_rootWeight, hD.2.2.2.2.2.1 a b]
  have hfg := Module.Dual.eq_of_preReflection_mapsTo' (Set.finite_range _)
    (Submodule.subset_span (s := roots) (Set.mem_range_self a)) hf hfroot hg hgroot
  intro b t
  have hb := LinearMap.congr_fun hfg
    ⟨Additive.ofMul (D.rootWeight b), Submodule.subset_span (Set.mem_range_self b)⟩
  change characterCocharacterPairing T C.cocharacter (Additive.ofMul (D.rootWeight b)) =
    D.characterCorootPairing a (Additive.ofMul (D.rootWeight b)) at hb
  rw [hD.characterCorootPairing_rootWeight] at hb
  exact (characterCocharacterPairing_spec T (D.rootWeight b) C.cocharacter t).trans
    (congrArg (fun m : ℤ => (dPointEquiv 1 t 0 : k) ^ m) hb)

end RootGroupData

namespace RootSystemModel
variable {G : Variety k} [AlgebraicGroup G]
variable (M : RootSystemModel typeF4RootPairingULift G)
local instance normalizationModelTorusAlgebraicGroup : AlgebraicGroup M.torus.carrierVariety :=
  M.torus.carrierAlgebraicGroup

/-- Every chart on an actual F4 simple root has the source Cartan normalization.
The numbered standard root need not lie in the model's chosen positive base. -/
theorem f4_binaryOppositeRootSL2Chart_isCartan (i : Fin 4)
    (C : BinaryOppositeRootSL2Chart M.torus (M.rootData.rootSubgroup (M.f4SimpleRoot i))
      (M.rootData.rootSubgroup (M.rootData.neg (M.f4SimpleRoot i)))) :
    M.rootData.IsCartanRootCocharacter (M.f4SimpleRoot i) C.cocharacter := by
  let : Finite M.rootData.Root := Finite.of_injective M.rootEquiv M.rootEquiv.injective
  exact M.rootData.chart_isCartan M.realization M.maximalTorus.1 (M.f4SimpleRoot i) C

end RootSystemModel

end Theory.AlgebraicGroup
