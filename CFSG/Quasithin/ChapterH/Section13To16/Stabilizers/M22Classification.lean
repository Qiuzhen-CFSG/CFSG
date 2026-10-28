module

public import Theory.Mathieu.M22.ChapterHLocalClassification
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms.Compatibility

/-!
# Native inner and outer local groups in H.14.3

Both intrinsic hexad kernels are the actual pointwise octad E16, under the
native inclusion maps. The intrinsic quotients act as A6 and S6 on the six
source coordinates. The earlier restriction inputs required by H.15.2 and
H.16.4 are constructed, including the actual involution displacements.

The simultaneous source Sylows and the proved quintet-core identities give the
exact elementary-subgroup catalogues in (1). The natural F4-plane action and
the five-dimensional indecomposable S5 action establish (2). The actual hexad
conjugation actions become the natural A6 and S6 modules through an explicit
comparison automorphism of the geometric six-coordinate marking, proving (3).
All earlier group and conjugation-module inputs of the named code/cocode
consumers are discharged. The pair overgroup is identified with Aut(M22) by
its literal conjugation action, and the inner inclusion becomes inner automorphisms.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, H.14.3(1--3),
printed p.397 (PDF p.408), with the marking and Sylow setup on p.396.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterH.Section13To16
open Sporadic.Mathieu MathieuCode
open MathieuCode.Hexad.CocodeAction.SixPointModel
open scoped IsMulCommutative

/-- Both concrete kernel-image premises of the hexad consumers are discharged. -/
theorem m22_hexad_kernel_images :
    (m22InnerHexadKernel m22SourceOctad).map m22Embedding =
        octadPointwiseKernel m22SourceOctad ∧
      (m22OuterHexadKernel m22SourceOctad).map m22PairStabilizer.subtype =
        octadPointwiseKernel m22SourceOctad :=
  ⟨M22ChapterH.Hexad.inner_kernel_image, M22ChapterH.Hexad.outer_kernel_image⟩

/-- The same elementary group occurs as the inner and outer hexad two-core. -/
theorem m22_hexad_kernels_elementary :
    IsElementaryAbelian 2 (m22InnerHexadKernel m22SourceOctad) ∧
      Nat.card (m22InnerHexadKernel m22SourceOctad) = 16 ∧
      IsElementaryAbelian 2 (m22OuterHexadKernel m22SourceOctad) ∧
      Nat.card (m22OuterHexadKernel m22SourceOctad) = 16 :=
  ⟨M22ChapterH.Hexad.inner_kernel_elementary, M22ChapterH.Hexad.inner_kernel_card,
    M22ChapterH.Hexad.outer_kernel_elementary, M22ChapterH.Hexad.outer_kernel_card⟩

/-- The inner quotient uses the actual A6 action on the source hexad. -/
def m22_innerHexad_quotient_equiv :
    (m22InnerHexadStabilizer O ⧸ pCore 2 (m22InnerHexadStabilizer O)) ≃* alternatingGroup H :=
  M22ChapterH.Hexad.innerQuotientEquiv

/-- The outer quotient uses the actual S6 action on that same hexad. -/
def m22_outerHexad_quotient_equiv :
    (m22OuterHexadStabilizer O ⧸ pCore 2 (m22OuterHexadStabilizer O)) ≃* Equiv.Perm H :=
  M22ChapterH.Hexad.outerQuotientEquiv

@[simp] theorem m22_innerHexad_quotient_equiv_mk (g : m22InnerHexadStabilizer O) :
    (m22_innerHexad_quotient_equiv (QuotientGroup.mk g) : Equiv.Perm H) =
      innerCoordinateAction g := M22ChapterH.Hexad.innerQuotientEquiv_mk g

@[simp] theorem m22_outerHexad_quotient_equiv_mk (g : m22OuterHexadStabilizer O) :
    m22_outerHexad_quotient_equiv (QuotientGroup.mk g) = outerCoordinateAction g :=
  M22ChapterH.Hexad.outerQuotientEquiv_mk g

/-- The earlier H.14 inputs of the native inner hexad code/cocode transfer. -/
theorem m22_innerHexad_restriction_input : MathieuCode.Hexad.InnerRestrictionInput O :=
  M22ChapterH.Hexad.innerRestriction

/-- The earlier H.14 inputs of the native outer hexad code/cocode transfer. -/
theorem m22_outerHexad_restriction_input : MathieuCode.Hexad.OuterRestrictionInput O :=
  M22ChapterH.Hexad.outerRestriction

/-- The source sextet action uses the certified pair-compatible marking. -/
theorem m22_sourceSextet_translation_action
    (g : Sporadic.Mathieu.M24LocalGeometry.sextetStabilizer m22SourceSextet)
    (v : Atlas.Codes.hexacode) :
    g.val * (M22ChapterH.Sextet.sourceTranslationEquiv (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      (M22ChapterH.Sextet.sourceTranslationEquiv (Multiplicative.ofAdd
        (Representation.Hexacode.action
          (Sporadic.Mathieu.M24LocalGeometry.SextetCore.quotientHom
            (M22ChapterH.Sextet.sourceStabilizerEquiv.symm g)) v))).val :=
  M22ChapterH.Sextet.sourceTranslationEquiv_conjugation g v

/-- The source translation candidates lie in the intrinsic local cores. -/
theorem m22_quintet_translation_inclusions :
    M22ChapterH.Sextet.innerTranslations ≤ m22InnerQuintetKernel m22SourceSextet ∧
      M22ChapterH.Sextet.outerTranslations ≤ m22OuterQuintetKernel m22SourceSextet :=
  ⟨M22ChapterH.Sextet.innerTranslations_le_core, M22ChapterH.Sextet.outerTranslations_le_core⟩

/-- The source overgroup M > L is the actual full automorphism group. -/
def m22_pairOvergroup_equiv : m22PairStabilizer ≃* MulAut M22 :=
  m22PairStabilizerEquivAut

theorem m22_pairOvergroup_equiv_conjugation (g : m22PairStabilizer) (k : M22) :
    m22Embedding (m22_pairOvergroup_equiv g k) =
      g.val * m22Embedding k * g.val⁻¹ := m22PairStabilizerEquivAut_apply g k

@[simp] theorem m22_pairOvergroup_equiv_inner (g : M22) :
    m22_pairOvergroup_equiv (m22ToPairStabilizer g) = MulAut.conj g :=
  m22PairStabilizerEquivAut_inner g

/-- The chosen ambient Sylow stabilizes all three source objects; both local
Sylows are its literal preimages, and the inner Sylow is T intersected with L. -/
theorem m22_compatible_sylows :
    M22ChapterH.CompatibleSylow.ambient.toSubgroup ≤
      Sporadic.Mathieu.M24LocalGeometry.octadStabilizer m22SourceOctad ∧
    M22ChapterH.CompatibleSylow.ambient.toSubgroup ≤
      Sporadic.Mathieu.M24LocalGeometry.sextetStabilizer m22SourceSextet ∧
    M22ChapterH.CompatibleSylow.ambient.toSubgroup ≤
      Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.trioStabilizer m22SourceTrio ∧
    M22ChapterH.CompatibleSylow.outer.toSubgroup =
      M22ChapterH.CompatibleSylow.ambient.toSubgroup.comap m22PairStabilizer.subtype ∧
    M22ChapterH.CompatibleSylow.inner.toSubgroup =
      M22ChapterH.CompatibleSylow.ambient.toSubgroup.comap m22Embedding ∧
    M22ChapterH.CompatibleSylow.inner.toSubgroup =
      M22ChapterH.CompatibleSylow.outer.toSubgroup.comap m22ToPairStabilizer :=
  M22ChapterH.CompatibleSylow.compatible

/-- H.14.3(1): both inner E16 subgroups, their distinctness, the literal
intersection KQ ∩ L, and the unique outer E32, with no core-recognition premises. -/
theorem lemma_H_14_3_1 :
    (m22InnerQuintetKernel m22SourceSextet).map m22ToPairStabilizer =
      m22OuterQuintetKernel m22SourceSextet ⊓ m22ToPairStabilizer.range ∧
    m22InnerHexadKernel m22SourceOctad ≠ m22InnerQuintetKernel m22SourceSextet ∧
    (∀ A : Subgroup M22,
      (IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
        A ≤ M22ChapterH.CompatibleSylow.inner.toSubgroup) ↔
      A = m22InnerHexadKernel m22SourceOctad ∨ A = m22InnerQuintetKernel m22SourceSextet) ∧
    (∀ A : Subgroup m22PairStabilizer,
      (IsElementaryAbelian 2 A ∧ Nat.card A = 32 ∧
        A ≤ M22ChapterH.CompatibleSylow.outer.toSubgroup) ↔
      A = m22OuterQuintetKernel m22SourceSextet) :=
  ⟨M22ChapterH.inner_quintet_map_pair, M22ChapterH.intrinsic_sylow_catalogue⟩

/-- The two inner alternatives, expressed as subgroups of the outer source group. -/
theorem m22_inner_sylow_kernel_images (A : Subgroup M22) (hA : IsElementaryAbelian 2 A)
    (hc : Nat.card A = 16) (hAS : A ≤ M22ChapterH.CompatibleSylow.inner.toSubgroup) :
    A.map m22ToPairStabilizer = m22OuterHexadKernel m22SourceOctad ∨
    A.map m22ToPairStabilizer =
      m22OuterQuintetKernel m22SourceSextet ⊓ m22ToPairStabilizer.range :=
  M22ChapterH.inner_sylow_kernel_images A hA hc hAS

open MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer

/-- The intrinsic outer quotient uses the actual action on the five remaining parts. -/
def m22_quintet_quotient_equiv : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 5) :=
  M22ChapterH.Quintet.quotientEquiv

@[simp] theorem m22_quintet_quotient_equiv_mk (g : Q) :
    m22_quintet_quotient_equiv (QuotientGroup.mk g) = NaturalQuotient.q g :=
  M22ChapterH.Quintet.quotientEquiv_mk g

/-- Both the six-part and five-part actions have the relative intrinsic two-core as kernel. -/
theorem m22_quintet_action_kernels :
    NaturalQuotient.partAction.ker = pCore 2 Q ∧
    NaturalQuotient.q.ker = pCore 2 Q :=
  ⟨M22ChapterH.Quintet.partAction_ker,
    NaturalQuotient.q_ker_eq_partAction_ker.trans M22ChapterH.Quintet.partAction_ker⟩

/-- The actual geometric L2(4) actor, in determinant-one matrix coordinates over F4. -/
def m22_quintet_natural_quotient_equiv :
    (M22ChapterH.Quintet.naturalActor ⧸ M22ChapterH.Quintet.naturalActorTranslations) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
  M22ChapterH.Quintet.naturalActorStandardEquiv

/-- Binary coordinates on KQ ∩ L in the natural F4 plane. -/
def m22_quintet_natural_coordinates : Additive A0 ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2) :=
  M22ChapterH.Quintet.innerCoreStandardEquiv

/-- H.14.3(2), inner clause: the genuine conjugation action is the natural L2(4) action. -/
theorem lemma_H_14_3_2_inner (a : M22ChapterH.Quintet.naturalActor) (v : Additive A0) :
    m22_quintet_natural_coordinates (innerConjugation M22ChapterH.Quintet.innerInputs a.val v) =
      Representation.specialLinearNatural 2
        (m22_quintet_natural_quotient_equiv (QuotientGroup.mk a))
        (m22_quintet_natural_coordinates v) :=
  M22ChapterH.Quintet.innerCore_standard_natural a v

/-- The same quotient identified with the source's genuine projective L2(4). -/
def m22_quintet_projective_quotient_equiv :
    (M22ChapterH.Quintet.naturalActor ⧸ M22ChapterH.Quintet.naturalActorTranslations) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
  M22ChapterH.Quintet.naturalActorProjectiveEquiv

/-- The projective formulation of the inner clause, using the unique SL2 lift. -/
theorem lemma_H_14_3_2_inner_projective
    (a : M22ChapterH.Quintet.naturalActor) (v : Additive A0) :
    m22_quintet_natural_coordinates (innerConjugation M22ChapterH.Quintet.innerInputs a.val v) =
      Representation.specialLinearNatural 2
        ((Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).symm
          (m22_quintet_projective_quotient_equiv (QuotientGroup.mk a)))
        (m22_quintet_natural_coordinates v) :=
  M22ChapterH.Quintet.innerCore_projective_natural a v

/-- The L2(4) actor really lies in native M22 and its kernel is the restriction of O2(Q). -/
theorem m22_quintet_natural_actor :
    (∀ a : M22ChapterH.Quintet.naturalActor, a.val.val ∈ L) ∧
    M22ChapterH.Quintet.naturalActorTranslations =
      (pCore 2 Q).comap M22ChapterH.Quintet.naturalActor.subtype :=
  ⟨M22ChapterH.Quintet.naturalActor_inner, M22ChapterH.Quintet.naturalActorTranslations_eq_core⟩

/-- H.14.3(2), outer clause: the actual elementary core is an indecomposable
five-dimensional module for the S5 quotient, with its literal action equation. -/
theorem lemma_H_14_3_2_outer :
    IsElementaryAbelian 2 K ∧ Nat.card K = 32 ∧
    Module.finrank (ZMod 2) (Additive K) = 5 ∧
    (∀ g : Q, M22ChapterH.Quintet.kernelS5Conjugation (NaturalQuotient.q g) =
      kernelConjugation g) ∧
    (∀ A B : Subrepresentation M22ChapterH.Quintet.kernelS5Conjugation,
      IsCompl A B → A = ⊥ ∨ B = ⊥) :=
  ⟨M22ChapterH.Quintet.core_elementary, M22ChapterH.Quintet.core_card,
    M22ChapterH.Quintet.kernel_finrank, M22ChapterH.Quintet.kernelS5Conjugation_q,
    M22ChapterH.Quintet.kernelS5Conjugation_indecomposable⟩

/-- The concrete normality, index-two and involution inputs of the transvection consumer. -/
theorem m22_quintet_inner_inputs : InnerInputs := M22ChapterH.Quintet.innerInputs

/-- The four-dimensional conjugation module required by the downstream inner consumer. -/
theorem m22_quintet_inner_irreducible :
    Module.finrank (ZMod 2) (Additive A0) = 4 ∧
    Representation.IsIrreducible (innerConjugation m22_quintet_inner_inputs) :=
  ⟨M22ChapterH.Quintet.innerIntersection_finrank, M22ChapterH.Quintet.innerConjugation_isIrreducible⟩

/-- The downstream outer consumer uses this same literal Q-conjugation representation. -/
theorem m22_quintet_kernel_indecomposable (A B : Subrepresentation kernelConjugation)
    (hAB : IsCompl A B) : A = ⊥ ∨ B = ⊥ :=
  M22ChapterH.Quintet.kernelConjugation_indecomposable A B hAB

/-- Application to the existing cocode quotient, with both earlier group premises discharged. -/
theorem m22_quintet_top_isIrreducible :
    Representation.IsIrreducible V6Subrepresentation.quotientRepresentation :=
  NaturalQuotient.top_isIrreducible m22_quintet_action_kernels.1 m22_quintet_quotient_equiv

open M22ChapterH.Hexad.Action

/-- The natural inner quotient marking includes the explicit six-coordinate comparison. -/
def m22_innerHexad_natural_quotient_equiv :
    (Inner ⧸ pCore 2 Inner) ≃* alternatingGroup (Fin 6) := Natural.innerMarking

/-- The natural outer quotient marking includes that same comparison automorphism. -/
def m22_outerHexad_natural_quotient_equiv :
    (Outer ⧸ pCore 2 Outer) ≃* Equiv.Perm (Fin 6) := Natural.outerMarking

/-- The old coordinate marking is preserved and the natural marking is its explicit composite. -/
theorem m22_hexad_natural_markings :
    (∀ q : Outer ⧸ pCore 2 Outer, m22_outerHexad_natural_quotient_equiv q =
      Natural.markingAutomorphism
        (SymplecticComparison.sixRelabeling.permCongrHom (m22_outerHexad_quotient_equiv q))) ∧
    (∀ q : Inner ⧸ pCore 2 Inner, (m22_innerHexad_natural_quotient_equiv q).val =
      Natural.markingAutomorphism
        (SymplecticComparison.sixRelabeling.permCongrHom (m22_innerHexad_quotient_equiv q).val)) :=
  ⟨Natural.outerMarking_apply, Natural.innerMarking_coe⟩

/-- Natural binary coordinates on the intrinsic inner core, normal in its own stabilizer. -/
def m22_innerHexad_natural_coordinates :
    pCore 2 Inner ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) := Natural.innerCore

/-- Natural binary coordinates on the intrinsic outer core. -/
def m22_outerHexad_natural_coordinates :
    pCore 2 Outer ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) := Natural.outerCore

/-- H.14.3(3), inner case: natural A6 action on the actual relative two-core. -/
theorem lemma_H_14_3_3_inner (g : Inner) (a : pCore 2 Inner) :
    (m22_innerHexad_natural_coordinates
      ⟨g * a.val * g⁻¹, (inferInstance : (pCore 2 Inner).Normal).conj_mem a.val a.property g⟩).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6)
        (m22_innerHexad_natural_quotient_equiv (QuotientGroup.mk g)).val
        (m22_innerHexad_natural_coordinates a).toAdd := Natural.innerCore_conjugation g a

/-- H.14.3(3), outer case: natural S6 action on the same E16 in the pair overgroup. -/
theorem lemma_H_14_3_3_outer (g : Outer) (a : pCore 2 Outer) :
    (m22_outerHexad_natural_coordinates
      ⟨g * a.val * g⁻¹, (inferInstance : (pCore 2 Outer).Normal).conj_mem a.val a.property g⟩).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6)
        (m22_outerHexad_natural_quotient_equiv (QuotientGroup.mk g))
        (m22_outerHexad_natural_coordinates a).toAdd := Natural.outerCore_conjugation g a

/-- The hexad module in (3) is four-dimensional over the binary field. -/
theorem m22_hexad_natural_dimension :
    Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 6)) = 4 := by
  simpa using BinaryPermutation.finrank_natural_even (Fin 6) (by decide)

/-- Native H.14 also supplies the exact map-kernel conjugation convention used
by the later elementary-four arguments. -/
theorem m22_hexad_map_kernel_action (g : Outer) (a : Natural.outerMap.ker) :
    Natural.outerMapCoordinates
      ⟨g * a.val * g⁻¹, (inferInstance : Natural.outerMap.ker.Normal).conj_mem a.val a.property g⟩ =
      BinaryPermutation.naturalRepresentation (Fin 6) (Natural.outerMap g)
        (Natural.outerMapCoordinates a) := Natural.outerMapCoordinates_conjugation g a

end CFSG.Quasithin.ChapterH.Section13To16
end
