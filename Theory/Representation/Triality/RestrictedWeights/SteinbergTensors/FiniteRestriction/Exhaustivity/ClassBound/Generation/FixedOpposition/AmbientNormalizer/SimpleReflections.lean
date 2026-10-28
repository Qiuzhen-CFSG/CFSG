module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.ReflectionWords
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.WordConstruction
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.Coordinates

/-!
# Ambient simple reflections from normalized D4 coroot words

For each marked simple root, take the source word `n_i(1)`. The realized
root-weight equations scale its three factors simultaneously. If the
normalized words recover the supplied coroots, rearranging that equality
shows that `n_i(1)` implements the canonical point reflection on the entire
torus. The coordinate comparison then gives its action on every integral
weight. Character separation proves involutivity and actual normalizer
membership; the representatives also lie in their opposite-root pairs by
`SimpleRootParameters.word_mem`.

The construction is conditional on `SimpleCorootWordData`. Its existence,
and therefore unconditional existence of `SimpleReflectionLifts`, remains
a separate geometric obligation. No choice of representatives depending
on the individual torus point is used.

Sources: GLS3, `refs/KGroup/GLS3/Chapter1.tex`, Theorem 1.9.5(f),
Remarks 1.9.6 and Section 1.12; Steinberg, `Chapter2St2.tex`, Sections 6 and 12.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
/-- The one element `n_i(1)` implements inverse conjugation on every torus
point by the canonical simple-reflection formula. -/
theorem SimpleCorootWordData.conjugation {S : Geometry K} (C : SimpleCorootWordData S)
    (i : Fin 4) (t : Variety.Point S.torus.carrierVariety) :
    S.torus.includePoint t * (C.parameters i).word 1 =
      (C.parameters i).word 1 *
        S.torus.includePoint (AmbientCount.TorusGeometry.simpleReflection S i t) := by
  let a := (S.simpleRoot i).val
  let z := (S.roots.rootWeight a).onPoints t
  let h := S.torus.includePoint ((S.roots.rootCocharacter a).onPoints z)
  let n := (C.parameters i).word 1
  let Tt := S.torus.includePoint t
  have hword : (C.parameters i).word (dPointEquiv 1 z 0) = n * h := by
    dsimp [h, n]
    rw [C.coroot_eq]
    group
  have hc : Tt⁻¹ * n * Tt = n * h :=
    ((C.parameters i).word_conjugation t).trans hword
  calc
    Tt * n = Tt * (n * h) * h⁻¹ := by group
    _ = Tt * (Tt⁻¹ * n * Tt) * h⁻¹ := by rw [hc]
    _ = n * (Tt * h⁻¹) := by group
    _ = _ := by
      change _ = n * S.torus.inclusion.onPoints
        (t * ((S.roots.rootCocharacter a).onPoints z)⁻¹)
      rw [map_mul, map_inv]
      rfl

/-- Normalized opposite-root words give the four simultaneous lifts, with
the all-weight character equation supplied by the actual torus coordinates. -/
def SimpleCorootWordData.toSimpleReflectionLifts {S : Geometry K}
    (C : SimpleCorootWordData S) : SimpleReflectionLifts S where
  representative i := (C.parameters i).word 1
  torusMap := AmbientCount.TorusGeometry.simpleReflection S
  conjugation := C.conjugation
  character := AmbientCount.TorusGeometry.simpleReflection_weight S

/-- The canonical point map is an involution, by character separation and
the D4 Cartan diagonal. No ambient representative is needed for this fact. -/
theorem simpleReflection_involutive (S : Geometry K) (i : Fin 4) :
    Function.Involutive (AmbientCount.TorusGeometry.simpleReflection S i) := by
  intro t
  apply (torusPointEval_bijective S.maximalTorus.1).1
  ext χ
  obtain ⟨a, rfl⟩ := S.weight.surjective χ
  change (S.weight (Multiplicative.ofAdd a.toAdd)).pointCharacter
    (AmbientCount.TorusGeometry.simpleReflection S i
      (AmbientCount.TorusGeometry.simpleReflection S i t)) =
    (S.weight a).pointCharacter t
  rw [AmbientCount.TorusGeometry.simpleReflection_weight,
    AmbientCount.TorusGeometry.simpleReflection_weight]
  have href : D4RestrictedWeight.reflection i (D4RestrictedWeight.reflection i a.toAdd) =
      a.toAdd := by
    funext j
    have hdiag : typeDCartanMatrix 2 i i = 2 := by
      fin_cases i <;> rfl
    simp only [D4RestrictedWeight.reflection, hdiag]
    ring
  rw [href]
  rfl

/-- The same representative also implements left conjugation, since the
canonical reflection is an involution. -/
theorem SimpleCorootWordData.left_conjugation {S : Geometry K}
    (C : SimpleCorootWordData S) (i : Fin 4)
    (t : Variety.Point S.torus.carrierVariety) :
    (C.parameters i).word 1 * S.torus.includePoint t * ((C.parameters i).word 1)⁻¹ =
      S.torus.includePoint (AmbientCount.TorusGeometry.simpleReflection S i t) := by
  have h := C.conjugation i (AmbientCount.TorusGeometry.simpleReflection S i t)
  rw [simpleReflection_involutive S i t] at h
  calc
    _ = (S.torus.includePoint (AmbientCount.TorusGeometry.simpleReflection S i t) *
      (C.parameters i).word 1) * ((C.parameters i).word 1)⁻¹ := by rw [h]
    _ = _ := by group

/-- The word representative lies in the normalizer of the actual supplied
torus, rather than only acting on its abstract weight lattice. -/
theorem SimpleCorootWordData.mem_normalizer {S : Geometry K}
    (C : SimpleCorootWordData S) (i : Fin 4) :
    (C.parameters i).word 1 ∈ S.torus.normalizer.toSubgroup := by
  change (C.parameters i).word 1 ∈ Subgroup.normalizer (S.torus.toSubgroup : Set _)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨t, rfl⟩ := (Set.ext_iff.mp S.torus.range_inclusion x).mpr hx
    change (C.parameters i).word 1 * S.torus.includePoint t *
      ((C.parameters i).word 1)⁻¹ ∈ S.torus
    rw [C.left_conjugation]
    exact (S.torus.pointEquiv _).property
  · intro hx
    obtain ⟨t, ht⟩ := (Set.ext_iff.mp S.torus.range_inclusion _).mpr hx
    change S.torus.includePoint t =
      (C.parameters i).word 1 * x * ((C.parameters i).word 1)⁻¹ at ht
    have hx_eq : x = S.torus.includePoint
        (AmbientCount.TorusGeometry.simpleReflection S i t) := by
      have h := C.conjugation i t
      rw [ht] at h
      calc
        _ = ((C.parameters i).word 1)⁻¹ *
          (((C.parameters i).word 1 * x * ((C.parameters i).word 1)⁻¹) *
            (C.parameters i).word 1) := by group
        _ = _ := by rw [h]; group
    rw [hx_eq]
    exact (S.torus.pointEquiv _).property

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer
