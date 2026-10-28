module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.LocalPresentation
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SuzukiConvention

/-!
# Finite local Suzuki presentation in the full Ree group

The field charts supply a canonical finite table on one negative Suzuki root
and the full two-parameter Cartan. The proved native norm identity verifies the
Gauss relator. Two-cell collection then proves the evaluation kernel trivial:
the short cell separates the root from the Cartan, and the long cell cannot
contain the identity because the literal reflection is outside the conjugate
Borel. The result identifies the presentation with the actual generated local
subgroup of `ReeF4.Model m`, uniformly including `m = 0`.

This is the local reduction used in the twisted Bruhat argument of Steinberg,
*Lectures on Chevalley Groups*, Section 11, Lemmas 62--64. It is not a
presentation of the full Ree group; mixed relative-root collection remains
separate. All native equations are inherited from `NativeRankOne` and
`SuzukiConvention` with their checked coordinate convention.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.SuzukiPresentation
open Subgroup Parabolics LargeLocalSeeds
open LocalBlockInput.PairRigidity LocalBlockInput.PairRigidity.LocalIndices
open LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open SuzukiConvention
variable {m : ℕ}

/-- The parameter group is one native root, not the ambient Ree carrier. Its
field multiplication is `SuzukiConvention.nativeChartEquiv_mul`. -/
abbrev Parameter (m : ℕ) := rootBlock m .suzuki false

def coordinates (a : Parameter m) : CoefficientField m × CoefficientField m :=
  (nativeChartEquiv m false).symm a

@[simp] theorem root_coordinates (a : Parameter m) :
    suzuki m false (coordinates a).1 (coordinates a).2 = a := by
  simpa only [nativeChartEquiv_apply,coordinates] using
    congrArg Subtype.val ((nativeChartEquiv m false).apply_symm_apply a)

@[simp] theorem coordinates_root (a : CoefficientField m × CoefficientField m) :
    coordinates (nativeChartEquiv m false a) = a := (nativeChartEquiv m false).symm_apply_apply a

@[simp] theorem coordinates_one : coordinates (1 : Parameter m) = (0,0) := by
  rw [← nativeChartEquiv_zero false,coordinates_root]

theorem coordinates_mul (a b : Parameter m) :
    coordinates (a*b) = nativeMul (coordinates a) (coordinates b) := by
  apply (nativeChartEquiv m false).injective
  simp only [coordinates,Equiv.apply_symm_apply,nativeChartEquiv_mul]

theorem norm_coordinates_ne_zero (a : Parameter m) (ha : a ≠ 1) :
    norm (coordinates a).1 (coordinates a).2 ≠ 0 := by
  apply norm_ne_zero
  by_contra! hz
  apply ha
  apply Subtype.ext
  rw [← root_coordinates a,hz.1,hz.2,suzuki_zero]
  rfl

/-- Canonical finite local tables, on a group of q² root parameters and the
full two-dimensional Cartan. The nontrivial Gauss entry is the proved norm formula. -/
def table (m : ℕ) : LocalPresentation.Table (Parameter m) (TorusParameter m) := by
  classical
  exact {
    action t a := nativeChartEquiv m false
      ((signedScale t.2 false : CoefficientField m)*(coordinates a).1,
        (signedScale (centralScale t.2) false : CoefficientField m)*(coordinates a).2)
    torusReflection := torusReflection m .suzuki
    gaussLeft a := nativeChartEquiv m false
      (negativeFirst (coordinates a).1 (coordinates a).2,
        negativeSecond (coordinates a).1 (coordinates a).2)
    gaussTorus a := if hn : norm (coordinates a).1 (coordinates a).2 ≠ 0 then
      suzukiTau (Units.mk0 (norm (coordinates a).1 (coordinates a).2) hn) else 1
    gaussRight a := nativeChartEquiv m false
      (positiveFirst (coordinates a).1 (coordinates a).2,
        positiveSecond (coordinates a).1 (coordinates a).2) }

/-- The action table agrees with the literal negative field characters. -/
theorem table_action (t : TorusParameter m) (a : Parameter m) :
    coordinates ((table m).action t a) =
      ((signedScale t.2 false : CoefficientField m)*(coordinates a).1,
        (signedScale (centralScale t.2) false : CoefficientField m)*(coordinates a).2) := by
  exact coordinates_root _

/-- The finite action table evaluates with exactly the signed torus characters. -/
theorem native_torus_root (t : TorusParameter m) (a : Parameter m) :
    torus m t*(a : Model m)*(torus m t)⁻¹ = ((table m).action t a : Model m) := by
  have he := torus_suzuki t false (coordinates a).1 (coordinates a).2
  rw [root_coordinates a] at he
  have hb : ((table m).action t a : Model m) =
      suzuki m false ((signedScale t.2 false : CoefficientField m)*(coordinates a).1)
        ((signedScale (centralScale t.2) false : CoefficientField m)*(coordinates a).2) :=
    nativeChartEquiv_apply (m := m) false _
  exact he.trans hb.symm

/-- The native Gauss entry evaluates without unfolding the other table fields. -/
theorem native_gauss (a : Parameter m) (ha : a ≠ 1) :
    reflection m .suzuki*(a : Model m)*reflection m .suzuki =
      ((table m).gaussLeft a : Model m)*torus m ((table m).gaussTorus a)*
        reflection m .suzuki*((table m).gaussRight a : Model m) := by
  have hn := norm_coordinates_ne_zero a ha
  have he := suzuki_gauss_conjugate (coordinates a).1 (coordinates a).2 hn
  rw [root_coordinates a] at he
  have ht : (table m).gaussTorus a =
      suzukiTau (Units.mk0 (norm (coordinates a).1 (coordinates a).2) hn) := dif_pos hn
  rw [ht]
  change _ = (nativeChartEquiv m false _ : Model m)*_ * _ * (nativeChartEquiv m false _ : Model m)
  rw [nativeChartEquiv_apply,nativeChartEquiv_apply]
  exact he

/-- Native verification of every local relator, including the full Cartan. -/
theorem native_equations (m : ℕ) :
    LocalPresentation.Equations (table m) (rootBlock m .suzuki false).subtype
      (torus m) (reflection m .suzuki) where
  involution := reflection_sq m .suzuki
  torus_root := native_torus_root
  weyl_torus t := by
    have hi : (reflection m .suzuki)⁻¹ = reflection m .suzuki :=
      inv_eq_of_mul_eq_one_right (reflection_sq m .suzuki)
    change reflection m .suzuki*torus m t*reflection m .suzuki = torus m (torusReflection m .suzuki t)
    simpa only [hi] using reflection_torus (m := m) .suzuki t
  gauss := native_gauss

/-- The actual generated local group with its complementary Cartan factor. -/
def generated (m : ℕ) : Subgroup (Model m) :=
  (rootBlock m .suzuki false).subtype.range ⊔ (torus m).range ⊔
    zpowers (reflection m .suzuki)

/-- The Borel conjugated by the same simple reflection separates its local cells. -/
def oppositeBorel (m : ℕ) : Subgroup (Model m) :=
  (borel m).comap (MulAut.conj (reflection m .suzuki)).toMonoidHom

private theorem positive_mem_borel (t u : CoefficientField m) :
    suzuki m true t u ∈ borel m := by
  let d := canonicalLocalBlockInput m
  have hp : (suzukiCoordinates d).element true t u ∈ rootBorel d :=
    (show standardUnipotent d ≤ rootBorel d from Subgroup.comap_mono le_sup_left)
      (simpleBlock_positive_le d .suzuki ((suzukiCoordinates d).element_mem true t u))
  rw [← rootBorel_map_modelEquiv d]
  exact mem_map_of_mem _ hp

/-- The native negative root lies in this actual conjugated Borel. -/
theorem root_le_oppositeBorel (m : ℕ) :
    (rootBlock m .suzuki false).subtype.range ≤ oppositeBorel m := by
  rintro y ⟨a,rfl⟩
  change reflection m .suzuki*a*(reflection m .suzuki)⁻¹ ∈ borel m
  rw [inv_eq_of_mul_eq_one_right (reflection_sq m .suzuki),← root_coordinates a,reflection_suzuki]
  exact positive_mem_borel _ _

theorem torus_le_oppositeBorel (m : ℕ) : (torus m).range ≤ oppositeBorel m := by
  rintro y ⟨t,rfl⟩
  change reflection m .suzuki*torus m t*(reflection m .suzuki)⁻¹ ∈ borel m
  have ht : torus m (torusReflection m .suzuki t) ∈ borel m :=
    fixedTorus_le_borel m ((torus_range m).le ⟨_,rfl⟩)
  exact (reflection_torus (m := m) .suzuki t).symm ▸ ht

private theorem self_not_mem_conjugate {G : Type*} [Group G] (B : Subgroup G) (n : G)
    (hn : n ∉ B) : n ∉ B.comap (MulAut.conj n).toMonoidHom := by
  intro h
  apply hn
  change n*n*n⁻¹ ∈ B at h
  simpa only [mul_inv_cancel_right] using h

theorem reflection_not_mem_oppositeBorel (m : ℕ) : reflection m .suzuki ∉ oppositeBorel m :=
  self_not_mem_conjugate (borel m) (reflection m .suzuki)
    (SmallCompletion.reflection_not_mem_borel m .suzuki)

theorem root_torus_disjoint (m : ℕ) :
    Disjoint (rootBlock m .suzuki false).subtype.range (torus m).range := by
  apply Subgroup.disjoint_def.mpr
  rintro y ⟨a,rfl⟩ ht
  let d := canonicalLocalBlockInput m
  have hx : d.modelEquiv.symm a ∈ simpleBlock d .suzuki false := by
    change (d.modelEquiv.symm a).val ∈ splitSimpleBlock m .suzuki false
    rw [modelEquiv_symm_coe]
    simpa only [rootBlock,mem_comap,toSplitGroup_apply] using a.property
  have hb : d.modelEquiv.symm a ∈ rootBorel d := by
    change (d.modelEquiv.symm a).val ∈ splitBorel m
    rw [modelEquiv_symm_coe]
    apply (le_sup_right : splitTorus m ≤ splitBorel m)
    rw [torus_range m] at ht
    simpa only [fixedTorus,mem_comap,toSplitGroup_apply,Subgroup.subtype_apply] using ht
  apply d.modelEquiv.symm.injective
  rw [map_one]
  exact Subgroup.disjoint_def.mp (negativeBlock_disjoint_rootBorel d (splitTorus_eq_diagonalTorus m) .suzuki) hx hb

/-- A fully proved local presentation of the native Suzuki root--Cartan subgroup.
The two-cell argument proves its evaluation kernel; native simplicity is not used. -/
def nativeEquiv (m : ℕ) : LocalPresentation.Presentation (table m) ≃* generated m :=
  LocalPresentation.realization (table m) (native_equations m)
    Subtype.val_injective (torus_injective m) (root_torus_disjoint m)
    (oppositeBorel m) (root_le_oppositeBorel m) (torus_le_oppositeBorel m)
    (reflection_not_mem_oppositeBorel m)

@[simp] theorem nativeEquiv_root (a : Parameter m) :
    (nativeEquiv m (LocalPresentation.root (table m) a) : Model m) = a :=
  LocalPresentation.eval_root (table m) (native_equations m) a

@[simp] theorem nativeEquiv_torus (t : TorusParameter m) :
    (nativeEquiv m (LocalPresentation.torus (table m) t) : Model m) = torus m t :=
  LocalPresentation.eval_torus (table m) (native_equations m) t

@[simp] theorem nativeEquiv_reflection :
    (nativeEquiv m (LocalPresentation.reflection (table m)) : Model m) = reflection m .suzuki :=
  LocalPresentation.eval_reflection (table m) (native_equations m)

end ReeF4.RootPresentationRecognition.SuzukiPresentation
