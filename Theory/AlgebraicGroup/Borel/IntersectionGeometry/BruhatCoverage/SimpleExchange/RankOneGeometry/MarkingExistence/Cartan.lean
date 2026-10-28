module

public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.Inputs
public import Theory.AlgebraicGroup.Instance.PSL
public import Theory.AlgebraicGroup.Morphism.SL2RootRegularity
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.TypeASLDiagonalTorus
public import Theory.AlgebraicGroup.RootSubgroups.Finite
public import Theory.AlgebraicGroup.RootSubgroups.MultiplicityOne
public import Theory.AlgebraicGroup.Tori.Character.FiniteGeneration
public import Theory.AlgebraicGroup.Tori.Power
public import Mathlib.LinearAlgebra.Reflection

/-!
Cartan normalization and root transport for a calibrated SL₂ marking.

The two regular root curves make the point homomorphism algebraic. Its inverse
matrix diagonal is therefore an algebraic cocharacter of the given torus.
The rank-one word formula shows that its reflection acts on torus characters
by a reflection with this cocharacter's integral functional. Both this
reflection and the supplied datum's reflection preserve the finite actual
root set. Uniqueness of reflection functionals on its span identifies their
Cartan integers. Root-subgroup uniqueness then identifies their closed images.

This extends the finite-character argument in
`TargetWords/Normalization.lean` for F4 binary charts to every characteristic;
the reflection need only square into the torus, rather than be an involution.
Sources: GLS3, 1.9.5(b)--(f), 1.9.6; Borel, §§13.18 and 14.6--14.8.
-/

universe u

namespace Theory.AlgebraicGroup.SL2RootMarking

open _root_.Matrix
open scoped MatrixGroups
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
variable {D : RootGroupData G T} {α : D.Root} (M : SL2RootMarking D α)

private theorem exists_algebraicHom :
    ∃ F : Morphism (slVariety k 2) G,
      F.onPoints = M.hom.comp (slPointMulEquiv (k := k) 2).toMonoidHom := by
  apply exists_sl2Morphism_of_regular_rootCurves _
    ((D.rootSubgroup α).inclusion.comp M.plus.hom)
    ((D.rootSubgroup (D.neg α)).inclusion.comp M.minus.hom)
  · intro s
    obtain ⟨t, rfl⟩ : ∃ t, kPlusPoint t = s := ⟨_, kPlusPoint_coordinate s⟩
    change M.hom (slPointMulEquiv 2 _) = _
    rw [slPointMulEquiv_apply]
    exact M.upper_eq t
  · intro s
    obtain ⟨t, rfl⟩ : ∃ t, kPlusPoint t = s := ⟨_, kPlusPoint_coordinate s⟩
    change M.hom (slPointMulEquiv 2 _) = _
    rw [slPointMulEquiv_apply]
    exact M.lower_eq t

/-- The homomorphism in a marking is regular because both root curves are. -/
public noncomputable def algebraicHom : Morphism (slVariety k 2) G :=
  Classical.choose M.exists_algebraicHom

public theorem algebraicHom_onPoints (x : Variety.Point (slVariety k 2)) :
    M.algebraicHom.onPoints x = M.hom (slPointMulEquiv 2 x) :=
  DFunLike.congr_fun (Classical.choose_spec M.exists_algebraicHom) x

private noncomputable def multiplicativeInverse : Morphism (KMult k) (KMult k) where
  toVariety := invMorphism (KMult k)
  map_one := inv_one
  map_mul := by
    intro x y
    change (x * y)⁻¹ = x⁻¹ * y⁻¹
    rw [_root_.mul_inv_rev]
    exact (isMulCommutative_iff.mp (dVariety_isMulCommutative 1)) _ _

private theorem diagonal_matrix (t : Variety.Point (KMult k)) :
    slPointMulEquiv 2 ((typeASLDiagonalMorphism (k := k) 1).onPoints t) =
      SpecialLinearGroup.diag2 (dPointEquiv 1 t 0 : k) (Units.ne_zero _) := by
  rw [slPointMulEquiv_apply]
  apply Subtype.ext
  change slPointMatrix 2 (typeASLDiagonalPoint 1 t) = _
  rw [typeASLDiagonalPoint_matrix]
  have h0 : typeASLDiagonalEntries 1 t 0 = dPointEquiv 1 t 0 :=
    typeASLDiagonalEntries_castSucc 1 t 0
  have h1 : typeASLDiagonalEntries 1 t 1 = (dPointEquiv 1 t 0)⁻¹ := by
    simpa using typeASLDiagonalEntries_last 1 t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [typeASLDiagonalMatrix, h0, h1, SpecialLinearGroup.diag2_coe']

private noncomputable def ambientCoroot : Morphism (KMult k) G :=
  M.algebraicHom.comp ((typeASLDiagonalMorphism 1).comp multiplicativeInverse)

private theorem ambientCoroot_apply (t : Variety.Point (KMult k)) :
    M.ambientCoroot.onPoints t =
      (M.hom (SpecialLinearGroup.diag2 (dPointEquiv 1 t 0 : k) (Units.ne_zero _)))⁻¹ := by
  change M.algebraicHom.onPoints ((typeASLDiagonalMorphism 1).onPoints t⁻¹) = _
  rw [M.algebraicHom_onPoints, ← map_inv, diagonal_matrix]
  rw [SpecialLinearGroup.diag2_inv]
  congr 1
  congr 1
  exact (dPoint_entry_inv 1 t 0).symm

/-- The source-convention coroot: the marking's image of `diag(t⁻¹,t)`.
Only its root-character evaluations are canonical; central factors of a
stored root cocharacter are not identified. -/
public noncomputable def coroot : ClosedSubgroupTorusCocharacter T :=
  M.ambientCoroot.codRestrictClosedSubgroup T fun t => by
    rw [M.ambientCoroot_apply]
    exact T.toSubgroup.inv_mem (M.diagonal_mem _ _)

public theorem coroot_inclusion (t : Variety.Point (KMult k)) :
    T.includePoint (M.coroot.onPoints t) =
      (M.hom (SpecialLinearGroup.diag2 (dPointEquiv 1 t 0 : k) (Units.ne_zero _)))⁻¹ := by
  change T.inclusion.onPoints (M.coroot.onPoints t) = _
  rw [coroot, Morphism.codRestrictClosedSubgroup_inclusion_apply,
    M.ambientCoroot_apply]

omit [IsAlgClosed k] in
private theorem diagonal_upper (a : k) (ha : a ≠ 0) (b : k) :
    SpecialLinearGroup.diag2 a ha * BruhatGeneration.SL2.upper b *
      (SpecialLinearGroup.diag2 a ha)⁻¹ = BruhatGeneration.SL2.upper (a ^ (2 : ℤ) * b) := by
  apply (mul_right_cancel_iff (a := SpecialLinearGroup.diag2 a ha)).mp
  simp only [mul_assoc, inv_mul_cancel, mul_one]
  apply Subtype.ext
  change (SpecialLinearGroup.diag2 a ha).val * (BruhatGeneration.SL2.upper b).val =
    (BruhatGeneration.SL2.upper (a ^ (2 : ℤ) * b)).val * (SpecialLinearGroup.diag2 a ha).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.diag2_coe', BruhatGeneration.SL2.upper,
      SpecialLinearGroup.transvection_coe, mul_apply, Fin.sum_univ_two]
  field_simp

/-- The inverse-conjugation weight of the coroot on its own upper curve is two. -/
public theorem coroot_self_weight (hD : D.IsRealization) :
    WeightCocharacterEquation T (D.rootWeight α) M.coroot 2 := by
  intro t
  have h := congrArg M.hom (diagonal_upper (dPointEquiv 1 t 0 : k) (Units.ne_zero _) 1)
  simp only [map_mul, map_inv, M.upper_eq, mul_one] at h
  have hw := (hD.2.2.1 α).2 M.plus 1 (M.coroot.onPoints t)
  rw [M.coroot_inclusion, inv_inv, mul_one] at hw
  have hp := (D.rootSubgroup α).inclusion_injective (hw.symm.trans h)
  have hq := M.plus.toMulEquiv.injective hp
  exact congrArg (fun z : Variety.Point (KPlus k) => z.val PUnit.unit) hq

private theorem reflection_conjugation (hD : D.IsRealization)
    (s : Variety.Point T.carrierVariety) :
    M.hom BruhatGeneration.SL2.reflection * T.includePoint s *
      (M.hom BruhatGeneration.SL2.reflection)⁻¹ =
        T.includePoint (s * (M.coroot.onPoints ((D.rootWeight α).onPoints s))⁻¹) := by
  obtain ⟨ha, heq⟩ := M.torus_conjugates_reflection hD s
  change _ = T.inclusion.onPoints _
  rw [map_mul, map_inv]
  change _ = T.includePoint s * (T.includePoint (M.coroot.onPoints _))⁻¹
  rw [M.coroot_inclusion, inv_inv]
  calc
    _ = T.includePoint s * ((T.includePoint s)⁻¹ *
        M.hom BruhatGeneration.SL2.reflection * T.includePoint s) *
        (M.hom BruhatGeneration.SL2.reflection)⁻¹ := by group
    _ = _ := by rw [heq]; simp only [mul_assoc, mul_inv_cancel, mul_one]; rfl

private theorem inverse_reflection_conjugation (hD : D.IsRealization)
    (hT : IsTorus T.carrierVariety) (s : Variety.Point T.carrierVariety) :
    (M.hom BruhatGeneration.SL2.reflection)⁻¹ * T.includePoint s *
      M.hom BruhatGeneration.SL2.reflection =
        T.includePoint (s * (M.coroot.onPoints ((D.rootWeight α).onPoints s))⁻¹) := by
  let w := M.hom BruhatGeneration.SL2.reflection
  have hsq : w * w ∈ T.toSubgroup := by
    dsimp [w]
    rw [← map_mul, BruhatGeneration.SL2.reflection_square]
    exact M.diagonal_mem _ _
  let q := T.pointEquiv.symm ⟨w * w, hsq⟩
  have hq : T.includePoint q = w * w :=
    congrArg Subtype.val (T.pointEquiv.apply_symm_apply _)
  have hcomm : T.includePoint s * (w * w) = (w * w) * T.includePoint s := by
    rw [← hq]
    exact congrArg T.inclusion.onPoints (isMulCommutative_iff.mp hT.isMulCommutative s q)
  change w⁻¹ * T.includePoint s * w = _
  calc
    _ = w⁻¹ * (T.includePoint s * (w * w)) * w⁻¹ := by group
    _ = w⁻¹ * ((w * w) * T.includePoint s) * w⁻¹ := by rw [hcomm]
    _ = w * T.includePoint s * w⁻¹ := by group
    _ = _ := M.reflection_conjugation hD s

end Theory.AlgebraicGroup.SL2RootMarking

namespace Theory.AlgebraicGroup.SL2RootMarking
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
variable {D : RootGroupData G T} {α : D.Root} (M : SL2RootMarking D α)

/-- Conjugating a root curve by the marked reflection changes its weight by
an integral multiple of the marked root. The coefficient is computed from
the actual diagonal cocharacter. -/
public theorem reflected_weight_equation (hD : D.IsRealization)
    (hT : IsTorus T.carrierVariety) {X : ClosedSubgroup G} {χ : TorusWeight T}
    (hχ : RootWeightEquation T X χ) :
    RootWeightEquation T (X.conjugate (M.hom BruhatGeneration.SL2.reflection))
      (χ * D.rootWeight α ^ (-characterCocharacterPairing T M.coroot (Additive.ofMul χ))) := by
  intro x a s
  let w := M.hom BruhatGeneration.SL2.reflection
  let e := X.conjugateIso w
  let y : OneParameterParametrization X.carrierVariety := e.symm.comp x
  let s₀ := s * (M.coroot.onPoints ((D.rootWeight α).onPoints s))⁻¹
  have hs : T.inclusion.onPoints s₀ = w⁻¹ * T.inclusion.onPoints s * w :=
    (M.inverse_reflection_conjugation hD hT s).symm
  have hy (c : k) : X.inclusion.onPoints (y.value c) =
      w⁻¹ * (X.conjugate w).inclusion.onPoints (x.value c) * w :=
    X.conjugateIso_inv_inclusion_apply w (x.value c)
  have hv : χ.pointCharacter s₀ =
      (χ * D.rootWeight α ^ (-characterCocharacterPairing T M.coroot (Additive.ofMul χ))).pointCharacter s := by
    dsimp [s₀]
    rw [map_mul, map_inv, characterCocharacterPairing_spec]
    change χ.pointCharacter s * (((D.rootWeight α).pointCharacter s) ^
      characterCocharacterPairing T M.coroot (Additive.ofMul χ))⁻¹ = _
    have h := congrArg Units.val ((torusPointEval T.carrierVariety s).map_mul χ
      (D.rootWeight α ^ (-characterCocharacterPairing T M.coroot (Additive.ofMul χ))))
    rw [map_zpow] at h
    have heval (ψ : TorusWeight T) : ψ.pointCharacter s =
        (torusPointEval T.carrierVariety s ψ : k) := rfl
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val] at h
    rw [heval, heval, heval]
    simpa only [zpow_neg] using h.symm
  have h := hχ y a s₀
  change (T.inclusion.onPoints s₀)⁻¹ * X.inclusion.onPoints (y.value a) *
    T.inclusion.onPoints s₀ = X.inclusion.onPoints (y.value (χ.pointCharacter s₀ * a)) at h
  rw [hs, hy, hv, hy] at h
  change (T.inclusion.onPoints s)⁻¹ * (X.conjugate w).inclusion.onPoints (x.value a) *
    T.inclusion.onPoints s = (X.conjugate w).inclusion.onPoints (x.value _)
  apply (MulAut.conj w⁻¹).injective
  simp only [MulAut.conj_apply, inv_inv]
  calc
    _ = (w⁻¹ * T.inclusion.onPoints s * w)⁻¹ *
        (w⁻¹ * (X.conjugate w).inclusion.onPoints (x.value a) * w) *
        (w⁻¹ * T.inclusion.onPoints s * w) := by group
    _ = _ := h

/-- The diagonal of any calibrated marking has the supplied Cartan exponents
on all roots. No simplicity of the marked root or reductivity is needed. -/
public theorem coroot_cartan (hD : D.IsRealization)
    (hT : IsTorus T.carrierVariety) (β : D.Root) :
    WeightCocharacterEquation T (D.rootWeight β) M.coroot (D.pairing β α) := by
  let : IsMulTorsionFree (TorusWeight T) :=
    torusCharacter_isTorsionFree_of_isConnected T.carrierVariety hT.isConnected
  let roots : Set (Additive (TorusWeight T)) := Set.range (fun b => Additive.ofMul (D.rootWeight b))
  have hfinite : roots.Finite := by
    have h := (torusRootSet_finite T).image Additive.ofMul
    rw [← hD.2.1, ← Set.range_comp] at h
    exact h
  let f := (characterCocharacterPairing T M.coroot).toIntLinearMap
  let g := (D.characterCorootPairing α).toIntLinearMap
  have hf : f (Additive.ofMul (D.rootWeight α)) = 2 :=
    (weightCocharacterEquation_existsUnique T (D.rootWeight α) M.coroot).unique
      (characterCocharacterPairing_spec T (D.rootWeight α) M.coroot)
      (M.coroot_self_weight hD)
  have hg : g (Additive.ofMul (D.rootWeight α)) = 2 := by
    change D.characterCorootPairing α (Additive.ofMul (D.rootWeight α)) = 2
    rw [hD.characterCorootPairing_rootWeight, hD.2.2.2.2.2.2.1 α]
  have heq (q : Additive (TorusWeight T) →ₗ[ℤ] ℤ) (b : D.Root) :
      Module.preReflection (Additive.ofMul (D.rootWeight α)) q
        (Additive.ofMul (D.rootWeight b)) =
          Additive.ofMul (D.rootWeight b * D.rootWeight α ^ (-q (Additive.ofMul (D.rootWeight b)))) := by
    change Additive.ofMul (D.rootWeight b / D.rootWeight α ^ q (Additive.ofMul (D.rootWeight b))) = _
    rw [div_eq_mul_inv, zpow_neg]
  have hfroot : Set.MapsTo (Module.preReflection (Additive.ofMul (D.rootWeight α)) f) roots roots := by
    rintro _ ⟨b, rfl⟩
    rw [heq]
    have hb : IsTorusRoot T (D.rootWeight b * D.rootWeight α ^
        (-characterCocharacterPairing T M.coroot (Additive.ofMul (D.rootWeight b)))) :=
      ⟨(D.rootSubgroup b).conjugate (M.hom BruhatGeneration.SL2.reflection),
        (hD.2.2.1 b).1.conjugate_of_mem_normalizer _ (M.reflection_mem hD),
        M.reflected_weight_equation hD hT (hD.2.2.1 b).2⟩
    have hb' : D.rootWeight b * D.rootWeight α ^
        (-characterCocharacterPairing T M.coroot (Additive.ofMul (D.rootWeight b))) ∈
          Set.range D.rootWeight := by
      rw [hD.2.1]
      exact hb
    obtain ⟨c, hc⟩ := hb'
    exact ⟨c, congrArg Additive.ofMul hc⟩
  have hgroot : Set.MapsTo (Module.preReflection (Additive.ofMul (D.rootWeight α)) g) roots roots := by
    rintro _ ⟨b, rfl⟩
    rw [heq]
    refine ⟨D.reflect α b, ?_⟩
    change Additive.ofMul (D.rootWeight (D.reflect α b)) =
      Additive.ofMul (D.rootWeight b * D.rootWeight α ^
        (-D.characterCorootPairing α (Additive.ofMul (D.rootWeight b))))
    rw [hD.characterCorootPairing_rootWeight, hD.2.2.2.2.2.1 α b]
  have hfg := Module.Dual.eq_of_preReflection_mapsTo' hfinite
    (Submodule.subset_span (s := roots) (Set.mem_range_self α)) hf hfroot hg hgroot
  have hb := LinearMap.congr_fun hfg
    ⟨Additive.ofMul (D.rootWeight β), Submodule.subset_span (Set.mem_range_self β)⟩
  change characterCocharacterPairing T M.coroot (Additive.ofMul (D.rootWeight β)) =
    D.characterCorootPairing α (Additive.ofMul (D.rootWeight β)) at hb
  rw [hD.characterCorootPairing_rootWeight] at hb
  intro t
  exact (characterCocharacterPairing_spec T (D.rootWeight β) M.coroot t).trans
    (congrArg (fun m : ℤ => (dPointEquiv 1 t 0 : k) ^ m) hb)

/-- The marked reflection has exactly the realized reflected root weight. -/
public theorem reflection_rootWeight (hD : D.IsRealization)
    (hT : IsTorus T.carrierVariety) (β : D.Root) :
    RootWeightEquation T ((D.rootSubgroup β).conjugate (M.hom BruhatGeneration.SL2.reflection))
      (D.rootWeight (D.reflect α β)) := by
  have h := M.reflected_weight_equation hD hT (hD.2.2.1 β).2
  have hm : characterCocharacterPairing T M.coroot (Additive.ofMul (D.rootWeight β)) =
      D.pairing β α :=
    (weightCocharacterEquation_existsUnique T (D.rootWeight β) M.coroot).unique
      (characterCocharacterPairing_spec T (D.rootWeight β) M.coroot)
      (M.coroot_cartan hD hT β)
  rw [hm, ← hD.2.2.2.2.2.1 α β] at h
  exact h

/-- Operational root multiplicity one identifies the conjugated closed
subgroup with the literal `D.reflect` root subgroup. -/
public theorem reflection_root_of_multiplicityOne (hD : D.IsRealization)
    (hT : IsTorus T.carrierVariety) (β : D.Root)
    (hmult : RootWeightSpaceMultiplicityOne T (D.rootWeight (D.reflect α β))) :
    (D.rootSubgroup β).conjugate (M.hom BruhatGeneration.SL2.reflection) =
      D.rootSubgroup (D.reflect α β) := by
  exact hmult.rootSubgroup_eq
    ((hD.2.2.1 β).1.conjugate_of_mem_normalizer _ (M.reflection_mem hD))
    (M.reflection_rootWeight hD hT β)
    (hD.2.2.1 (D.reflect α β)).1 (hD.2.2.1 (D.reflect α β)).2

end Theory.AlgebraicGroup.SL2RootMarking
