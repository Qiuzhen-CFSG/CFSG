module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.WeylPinning

/-!
# Orthogonal source pinnings from geometric normalization

A rank-one Weyl element is a product of an upper-root element, its Weyl
conjugate, and that same upper-root element. If it normalizes a subgroup
centralized by the upper-root element, the conjugate centralizes that
subgroup too. Consequently the Weyl element acts pointwise trivially.

Apply this to the third source short root and the highest long root. Their
setwise normalization is geometric; the two positive commutations come from
6E(b) and its Weyl conjugates. This constructs the orthogonal pointwise
stabilizers required by WeylPinning, leaving no signed action table as an
input. The actual two rank-one maps and the group braid are still source
construction obligations.

Source: Fong--Seitz I (1F), (6E)(b), and II (9.22)(iii), (9.25).
-/

@[expose] public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Theory.PSL2.SemilinearCoverage
open Triality.Standard Triality.Standard.RootPresentationRecognition
variable {F E Y : Type*} [Field F] [CharP F 2] [Field E] [CharP E 2] [Group Y]

/-- A Weyl word centralizes a normalized subgroup once its upper root does.
Only the unit upper-root element is needed. -/
theorem weyl_fixes_of_normalizes (f : SL2 F →* Y) (T : Subgroup Y)
    (hN : f (weyl F) ∈ Subgroup.normalizer (T : Set Y))
    (hU : ∀ x ∈ T, Commute (f (uni 1)) x) (x : Y) (hx : x ∈ T) :
    MulAut.conj (f (weyl F)) x = x := by
  let b := f (weyl F)
  let u := f (uni 1)
  have hword : u * (b*u*b⁻¹) * u = b := by
    simpa only [map_mul, map_inv] using congrArg f (weyl_root_word (F := F))
  have hux : Commute u x := hU x hx
  have hy : b⁻¹*x*b ∈ T := (Subgroup.mem_normalizer_iff''.mp hN x).mp hx
  have hv := (hU _ hy).map (MulAut.conj b).toMonoidHom
  change Commute (b*u*b⁻¹) (b*(b⁻¹*x*b)*b⁻¹) at hv
  have hvx : Commute (b*u*b⁻¹) x := by
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hv
  have hbx := (hux.mul_left hvx).mul_left hux
  rw [hword] at hbx
  change b*x*b⁻¹ = x
  rw [hbx.eq, mul_assoc, mul_inv_cancel, mul_one]

/-- The third source short root, with its unshifted field origin. -/
def shortTail (f : SL2 F →* Y) (g : SL2 E →* Y) : Multiplicative F →* Y :=
  (MulAut.conj (f (weyl F))).toMonoidHom.comp
    ((MulAut.conj (g (weyl E))).toMonoidHom.comp
      (f.comp (Matrix.SpecialLinearGroup.upperUnipotentHom F)))

/-- The highest source long root. -/
def longTail (f : SL2 F →* Y) (g : SL2 E →* Y) : Multiplicative E →* Y :=
  (MulAut.conj (g (weyl E))).toMonoidHom.comp
    ((MulAut.conj (f (weyl F))).toMonoidHom.comp
      (g.comp (Matrix.SpecialLinearGroup.upperUnipotentHom E)))

variable {σ : F ≃+* F}
local notation "K" => ScalarMarking.SourceFixed (σ := σ)

/-- Geometric root normalization and the two source positive commutations.
No pointwise Weyl action is an input. -/
structure GeometricPair (σ : F ≃+* F) (Y : Type*) [Group Y] where
  shortMap : SL2 F →* Y
  longMap : SL2 (ScalarMarking.SourceFixed (σ := σ)) →* Y
  braid : (shortMap (weyl F) * longMap (weyl _)) ^ 6 = 1
  shortNormalized : longMap (weyl _) ∈ Subgroup.normalizer ((shortTail shortMap longMap).range : Set Y)
  longNormalized : shortMap (weyl F) ∈ Subgroup.normalizer ((longTail shortMap longMap).range : Set Y)
  shortCommute : ∀ t : F,
    Commute (longMap (uni 1)) (shortTail shortMap longMap (.ofAdd t))
  longCommute : ∀ t : ScalarMarking.SourceFixed (σ := σ),
    Commute (shortMap (uni 1)) (longTail shortMap longMap (.ofAdd t))

namespace GeometricPair
variable (g : GeometricPair σ Y)

/-- Derive both orthogonal pointwise actions using the rank-one Weyl words. -/
def toRankOnePair : RankOnePair σ Y where
  shortMap := g.shortMap
  longMap := g.longMap
  braid := g.braid
  orthogonalShort t := by
    apply weyl_fixes_of_normalizes g.longMap (shortTail g.shortMap g.longMap).range
      g.shortNormalized
    · rintro x ⟨u,rfl⟩
      exact g.shortCommute u.toAdd
    · exact ⟨.ofAdd t,rfl⟩
  orthogonalLong t := by
    apply weyl_fixes_of_normalizes g.shortMap (longTail g.shortMap g.longMap).range
      g.longNormalized
    · rintro x ⟨u,rfl⟩
      exact g.longCommute u.toAdd
    · exact ⟨.ofAdd t,rfl⟩

end GeometricPair
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
