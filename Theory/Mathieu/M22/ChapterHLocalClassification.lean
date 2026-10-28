module

public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadKernels
public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadInputs
public import Theory.Mathieu.M22.ChapterHLocalClassification.SextetRestriction
public import Theory.Mathieu.M22.ChapterHLocalClassification.Sylow
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet
public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# Native inner and outer M22 local classification

The inner and outer intrinsic hexad kernels map onto the same pointwise octad
E16. Their literal six-coordinate actions identify the respective intrinsic
quotients with A6 and S6. Both kernel-image and displacement inputs to the
later hexad code and cocode transfers are discharged.
The source sextet's intrinsic E64 core has explicit hexacode coordinates.
Its inner and outer pair restrictions are the intrinsic quintet cores. Substituting
these proved identities into the compatible Sylow catalogue gives precisely the
two inner E16 subgroups and the unique outer E32 subgroup. The inner quintet
intersection is the natural F4 plane for its actual L2(4) subgroup; the outer
core is an indecomposable five-space for the literal five-part S5 quotient.

The hexad coordinates identify genuine conjugation with the natural binary
four-space, with the explicit comparison automorphism of the six-coordinate
quotient marking retained. Normality is relative to each stabilizer throughout.

Source: Aschbacher--Smith H.14.3(1--3), printed p.397, with the simultaneous
octad/sextet/trio Sylow arrangement on p.396. The imported branches construct
all group and module identifications; no classification premises remain below.
-/

public section
open Sporadic.Mathieu MathieuCode
namespace Sporadic.Mathieu.M22ChapterH

/-- The inner intrinsic quintet core is literally the outer core intersected with M22. -/
theorem inner_quintet_map_pair :
    (m22InnerQuintetKernel m22SourceSextet).map m22ToPairStabilizer =
      m22OuterQuintetKernel m22SourceSextet ⊓ m22ToPairStabilizer.range :=
  CompatibleSylow.intrinsic_inner_intersection
    Quintet.innerTranslations_eq_core Quintet.outerTranslations_eq_core

/-- The unconditional intrinsic-core catalogue for the simultaneous source Sylows. -/
theorem intrinsic_sylow_catalogue :
    m22InnerHexadKernel m22SourceOctad ≠ m22InnerQuintetKernel m22SourceSextet ∧
    (∀ A : Subgroup M22,
      (IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧ A ≤ CompatibleSylow.inner.toSubgroup) ↔
        A = m22InnerHexadKernel m22SourceOctad ∨ A = m22InnerQuintetKernel m22SourceSextet) ∧
    (∀ A : Subgroup m22PairStabilizer,
      (IsElementaryAbelian 2 A ∧ Nat.card A = 32 ∧ A ≤ CompatibleSylow.outer.toSubgroup) ↔
        A = m22OuterQuintetKernel m22SourceSextet) :=
  CompatibleSylow.intrinsic_catalogue
    Quintet.innerTranslations_eq_core Quintet.outerTranslations_eq_core

/-- The inner catalogue in the source's outer ambient group, with the literal inclusion. -/
theorem inner_sylow_kernel_images (A : Subgroup M22) (hA : IsElementaryAbelian 2 A)
    (hc : Nat.card A = 16) (hAS : A ≤ CompatibleSylow.inner.toSubgroup) :
    A.map m22ToPairStabilizer = m22OuterHexadKernel m22SourceOctad ∨
    A.map m22ToPairStabilizer =
      m22OuterQuintetKernel m22SourceSextet ⊓ m22ToPairStabilizer.range :=
  CompatibleSylow.intrinsic_inner_images
    Quintet.innerTranslations_eq_core Quintet.outerTranslations_eq_core A hA hc hAS

/-- The geometric five-part kernel equals the intrinsic two-core in the stabilizer. -/
theorem quintet_relative_kernel :
    MathieuCode.M22Quintet.CocodeTransfer.NaturalQuotient.q.ker =
      (m22OuterQuintetKernel m22SourceSextet).subgroupOf
        (m22OuterQuintetStabilizer m22SourceSextet) :=
  MathieuCode.M22Quintet.CocodeTransfer.NaturalQuotient.q_ker Quintet.partAction_ker

open MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer
open scoped IsMulCommutative

/-- The natural actor is the genuine projective L2(4) model: in characteristic
two the canonical SL2-to-PSL2 quotient is an isomorphism. -/
@[expose] noncomputable def Quintet.naturalActorProjectiveEquiv :
    (Quintet.naturalActor ⧸ Quintet.naturalActorTranslations) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
  Quintet.naturalActorStandardEquiv.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2))

/-- The action under the projective marking uses its unique determinant-one lift. -/
theorem Quintet.innerCore_projective_natural (a : Quintet.naturalActor) (v : Additive A0) :
    Quintet.innerCoreStandardEquiv (innerConjugation Quintet.innerInputs a.val v) =
      Representation.specialLinearNatural 2
        ((Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).symm
          (Quintet.naturalActorProjectiveEquiv (QuotientGroup.mk a)))
        (Quintet.innerCoreStandardEquiv v) := by
  rw [Quintet.naturalActorProjectiveEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  exact Quintet.innerCore_standard_natural a v

end Sporadic.Mathieu.M22ChapterH
