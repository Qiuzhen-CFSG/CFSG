module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Construction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.Assembly
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.SpecificGroups.LinearSylowNormalizers
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Higher-field Borel placement in 13.8.20

This file records the source-faithful reduction from `H` to the actual product
`K (L₁ T)` and supplies the intrinsic solvability needed by the published
local Borel construction.  The local action of `L₁ T` on the Borel is kept as
an explicit source-geometry hypothesis: it is the assertion proved from the
fixed-field Borel calculations in the surrounding 13.8 argument, rather than
an arbitrary subgroup being called a Borel.

Source: Aschbacher--Smith, proof of 13.8.20, printed p.954/PDF p.971.
-/

set_option linter.style.haveILetI false

@[expose] public section

open Subgroup
open scoped Pointwise
open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.Assembly
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source.Unitary

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Placement

variable {G : Type*} [Group G] [Finite G]
variable {H K L₁ T G₁ M : Subgroup G}
variable [hK : (Source.starImage H K).Normal]

/-! ## Intrinsic solvability -/

private theorem charP_two_of_card {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : CharP F 2 := by
  let _ := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)

private theorem g2_full_normalizer_isSolvable {F : Type*} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Atlas.G2.Model F)) :
    Group.IsSolvable (normalizer (S : Set (Atlas.G2.Model F))) := by
  let _ : Group.IsPerfect (Atlas.G2.Model F) := Atlas.G2.isPerfect (by
    rw [hF]
    have hn2 : 2 ≤ n := by omega
    exact lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by decide) hn2))
  let e : commutator (Atlas.G2.Model F) ≃* Atlas.G2.Model F :=
    (MulEquiv.subgroupCongr (Group.IsPerfect.commutator_eq_top (G := Atlas.G2.Model F))).trans
      Subgroup.topEquiv
  exact Sylow.isSolvable_normalizer_of_surjective e.toMonoidHom e.surjective
    (fun P : Sylow 2 (commutator (Atlas.G2.Model F)) =>
      Atlas.G2.DerivedNormalizerSolvable.isSolvable_normalizer_of_card (by omega) hF P) S

/-- Every one of the seven actual higher-field carriers has a solvable
Sylow-two normalizer.  The unitary branches use the fixed-field order `2^n`
and the matrix-field order `(2^n)^2` exactly as in the source. -/
theorem model_normalizer_isSolvable {D : Type*} [Group D] [Finite D]
    {n : ℕ} {unitary four : Bool} (model : Model D n unitary four)
    (hn : 1 < n) (S : Sylow 2 D) :
    Group.IsSolvable (normalizer (S : Set D)) := by
  cases model with
  | linearTwo F hF e hcover =>
    exact Sylow.isSolvable_normalizer_of_surjective e.symm.toMonoidHom e.symm.surjective
      (fun P => Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_psl_two_normalizer
        (by omega) hF P) S
  | specialLinearThree F hF e hcover =>
    exact Sylow.isSolvable_normalizer_of_surjective e.symm.toMonoidHom e.symm.surjective
      (fun P => Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_sl_three_normalizer
        (by omega) hF P) S
  | projectiveLinearThree F hF e hcover =>
    let _ : CharP F 2 := charP_two_of_card hF
    exact Sylow.isSolvable_normalizer_of_surjective e.symm.toMonoidHom e.symm.surjective
      (fun P => Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_projective_sylow_normalizer
        3 F (by decide) P) S
  | specialUnitaryThree E J hE hconj e hcover =>
    exact Sylow.isSolvable_normalizer_of_surjective e.symm.toMonoidHom e.symm.surjective
      (fun P => (CFSG.Quasithin.ChapterF.Source.rankOneSylowFacts_su3 J n (by omega) hE hconj P).solvable)
      S
  | projectiveUnitaryThree E J hE hconj e hcover =>
    haveI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective _ (suProjection_surjective J)
    exact Sylow.isSolvable_normalizer_of_surjective e.symm.toMonoidHom e.symm.surjective
      (fun P => (CFSG.Quasithin.ChapterF.Source.rankOneSylowFacts_psu3 J n (by omega) hE hconj P).solvable)
      S
  | symplecticFour F hF e hcover =>
    exact Sylow.isSolvable_normalizer_of_surjective e.symm.toMonoidHom e.symm.surjective
      (fun P => Theory.SpecificGroups.SymplecticFour.isSolvable_sylow_normalizer hF (by omega) P) S
  | g2 F hF e hcover =>
    let _ : CharP F 2 := charP_two_of_card hF
    exact Sylow.isSolvable_normalizer_of_surjective e.symm.toMonoidHom e.symm.surjective
      (fun P => g2_full_normalizer_isSolvable hF hn P) S

/-! ## The source reduction and Borel placement -/

/-- The normal overgroup used in the proof of 13.8.20.  All fields are source
standing data. The final placement theorem takes the genuine action of `L₁ T`
on the published Borel construction as its explicit source-geometry premise. -/
structure Setup (H K L₁ T G₁ M : Subgroup G)
    [hK : (Source.starImage H K).Normal] where
  mem_Hz : H ∈ Source.Hz L₁ T G₁ M
  component_le : K ≤ H
  component_normal : (K.subgroupOf H).Normal
  component_isComponent : (K.subgroupOf H).IsCComponent
  outside_M : ¬ K ≤ M
  base_le_H : L₁ ⊔ T ≤ H
  core_le_base : H.pCoreIn 2 ≤ L₁ ⊔ T
  core_normalized : G₁ ≤ normalizer (H.pCoreIn 2 : Set G)
  t_normalizes_l1 : T ≤ normalizer (L₁ : Set G)
  sylow : Chapter1.IsSylowIn 2 T H
  universal : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
    Group.IsSolvable J → J ≤ M
  base_solvable : Group.IsSolvable (L₁ ⊔ T : Subgroup G)

noncomputable def Setup.reduced (_s : Setup H K L₁ T G₁ M) : Subgroup G :=
  K ⊔ (L₁ ⊔ T)

omit [Finite G] in theorem Setup.reduced_mem_Hz (s : Setup H K L₁ T G₁ M) :
    s.reduced ∈ Source.Hz L₁ T G₁ M := by
  apply Components.normal_overgroup_mem_Hz L₁ T G₁ M H K _ s.mem_Hz
    s.component_le s.outside_M (s.mem_Hz.1.1) (isPGroup_pCoreIn 2 H)
  · exact s.core_le_base
  · exact s.core_normalized
  · exact s.component_normal

omit [Finite G] in theorem Setup.reduced_product (s : Setup H K L₁ T G₁ M) :
    ((s.reduced : Subgroup G) : Set G) = (K : Set G) * (L₁ : Set G) * (T : Set G) := by
  exact Components.normal_overgroup_product H K L₁ T s.component_le s.base_le_H
    s.component_normal s.t_normalizes_l1

omit [Finite G] in theorem Setup.reduced_component (s : Setup H K L₁ T G₁ M) :
    (K.subgroupOf s.reduced).IsCComponent := by
  exact s.component_isComponent.subgroupOf_of_le
    le_sup_left (sup_le s.component_le s.base_le_H)

universe u v

theorem model_transport {D E : Type u} [Group D] [Group E]
    {n : ℕ} {unitary four : Bool}
    (model : Model.{u, v} D n unitary four) (e : E ≃* D) :
    Model.{u, v} E n unitary four := by
  cases model with
  | linearTwo F hF e0 hcover => exact .linearTwo F hF (e.trans e0) hcover
  | specialLinearThree F hF e0 hcover => exact .specialLinearThree F hF (e.trans e0) hcover
  | projectiveLinearThree F hF e0 hcover =>
    exact .projectiveLinearThree F hF (e.trans e0) hcover
  | specialUnitaryThree E J hE hconj e0 hcover =>
    exact .specialUnitaryThree E J hE hconj (e.trans e0) hcover
  | projectiveUnitaryThree E J hE hconj e0 hcover =>
    exact .projectiveUnitaryThree E J hE hconj (e.trans e0) hcover
  | symplecticFour F hF e0 hcover => exact .symplecticFour F hF (e.trans e0) hcover
  | g2 F hF e0 hcover => exact .g2 F hF (e.trans e0) hcover

theorem Setup.reduced_model {G' : Type u} [Group G'] [Finite G']
    {H' K' L₁' T' G₁' M' : Subgroup G'}
    [hK' : (Source.starImage H' K').Normal]
    {n : ℕ} {unitary four : Bool}
    (s : Setup H' K' L₁' T' G₁' M')
    (model : Model.{u, v} (Source.starImage H' K') n unitary four)
    (hred : Source.starImage H' K' ≃* Source.starImage s.reduced K') :
    Model.{u, v} (Source.starImage s.reduced K') n unitary four :=
  model_transport model hred.symm

/-- Place the actual residual Borel in `M`, after the source local geometry has
identified its normalization by `L₁ T`. The normalization premise is stated
against this exact construction, whose intrinsic identity is exposed below. -/
theorem Setup.borel_star_identification (s : Setup H K L₁ T G₁ M) :
    Source.starImage H (borel H K T s.component_le s.sylow) =
      (borelResidual (normalizer (sourceSylow H K T s.sylow : Set
        (Source.starImage H K)))).map (Source.starImage H K).subtype :=
  borel_star_intrinsic H K T s.component_le s.sylow

theorem Setup.borel_le_M {n : ℕ} {unitary four : Bool}
    (s : Setup H K L₁ T G₁ M)
    (model : Model (Source.starImage H K) n unitary four) (hn : 1 < n)
    (hnorm : L₁ ⊔ T ≤ normalizer
      (borel H K T s.component_le s.sylow : Set G)) :
    borel H K T s.component_le s.sylow ≤ M := by
  apply borel_le_M_of_normalizes H K T L₁ G₁ M s.component_le s.sylow s.mem_Hz
    s.universal (model_normalizer_isSolvable model hn (sourceSylow H K T s.sylow))
    s.base_solvable hnorm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Placement

end
