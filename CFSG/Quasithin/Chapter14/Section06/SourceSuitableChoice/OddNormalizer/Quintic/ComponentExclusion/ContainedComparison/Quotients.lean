module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.NaturalBorel
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.PCoreImage

/-!
# Literal core images in the contained-component comparison

For A ≤ J, the map A → J/O₂(J) has two-group kernel. Removing the
intrinsic two-core of its actual image therefore recovers A/O₂(A),
compatibly with the original elements. This preserves the cyclic-five and
PSL₂(16) alternatives on K₁ without assuming O₂(K₁) ≤ O₂(J).

The contained source branch supplies five-rank one, B-normalization of
that same image, and O₂(J) ≤ B by relative normality and C.2.7 core control.
The row selection and block reconstruction are separate obligations.

Source: Aschbacher--Smith 14.6.15, printed p.1035; C.2.7, pp.145--147.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The literal image in the component's two-core quotient. -/
noncomputable def coreImage (J A : Subgroup G) : Subgroup (J ⧸ pCore 2 J) :=
  (A.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))

/-- Removing the intrinsic two-core of the image recovers the original
intrinsic two-core quotient. No inclusion of O₂(A) in O₂(J) is assumed. -/
noncomputable def coreImageQuotientEquiv {J A : Subgroup G} (h : A ≤ J) :
    (coreImage J A ⧸ pCore 2 (coreImage J A)) ≃* (A ⧸ pCore 2 A) := by
  let q := QuotientGroup.mk' (pCore 2 J)
  have hk : IsPGroup 2 (q.subgroupMap (A.subgroupOf J)).ker := by
    rw [Subgroup.ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  exact (MonoidHom.quotientPCoreEquivOfSurjective
    (q.subgroupMap (A.subgroupOf J)) (q.subgroupMap_surjective _) hk).symm.trans
      (QuotientGroup.congr _ _ (subgroupOfEquivOfLe h)
        (pCore_map_iso 2 (subgroupOfEquivOfLe h)))

/-- The comparison commutes with the original element and both quotient maps. -/
theorem coreImageQuotientEquiv_mk {J A : Subgroup G} (h : A ≤ J) (a : A) :
    coreImageQuotientEquiv h
      (QuotientGroup.mk' (pCore 2 (coreImage J A))
        ((QuotientGroup.mk' (pCore 2 J)).subgroupMap (A.subgroupOf J)
          ⟨⟨a,h a.property⟩,a.property⟩)) =
        QuotientGroup.mk' (pCore 2 A) a := by
  let q := QuotientGroup.mk' (pCore 2 J)
  have hk : IsPGroup 2 (q.subgroupMap (A.subgroupOf J)).ker := by
    rw [Subgroup.ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let e := MonoidHom.quotientPCoreEquivOfSurjective
    (q.subgroupMap (A.subgroupOf J)) (q.subgroupMap_surjective _) hk
  let x : A.subgroupOf J := ⟨⟨a,h a.property⟩,a.property⟩
  have hx : e.symm (QuotientGroup.mk' (pCore 2 (coreImage J A))
      ((q.subgroupMap (A.subgroupOf J)) x)) =
        QuotientGroup.mk' (pCore 2 (A.subgroupOf J)) x :=
    e.symm_apply_eq.mpr
      (MonoidHom.quotientPCoreEquivOfSurjective_mk
        (q.subgroupMap (A.subgroupOf J)) (q.subgroupMap_surjective _) hk x).symm
  exact congrArg (QuotientGroup.congr _ _ (subgroupOfEquivOfLe h)
    (pCore_map_iso 2 (subgroupOfEquivOfLe h))) hx

omit [Finite G] in
/-- Normalization is retained under the actual quotient projection. -/
theorem coreImage_normalizes {J A B : Subgroup G}
    (hn : B ≤ normalizer (A : Set G)) :
    coreImage J B ≤ normalizer (coreImage J A : Set (J ⧸ pCore 2 J)) := by
  have hn' : B.subgroupOf J ≤ normalizer (A.subgroupOf J : Set J) := by
    intro b hb
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (hn hb) (a : G)
  exact (map_mono hn').trans ((A.subgroupOf J).le_normalizer_map _)

variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)

local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : EscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

/-- Five-rank one survives the literal two-core quotient. -/
theorem component_core_rank (h : d.K1 ≤ j.J) :
    primeRank 5 (j.J ⧸ pCore 2 j.J) = 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [primeRank_quotient_eq_of_isTwoGroup 5 (by decide) (pCore 2 j.J) pCore_isPGroup]
  exact rank_one d j h

/-- The literal core-quotient image of the first factor has the two source
possibilities, with actual quotient isomorphisms. -/
theorem first_image_models (h : d.K1 ≤ j.J) :
    Nonempty ((coreImage j.J d.K1 ⧸ pCore 2 (coreImage j.J d.K1)) ≃*
      Multiplicative (ZMod 5)) ∨
    Nonempty ((coreImage j.J d.K1 ⧸ pCore 2 (coreImage j.J d.K1)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
  rcases d.models with hm | hm
  · obtain ⟨e⟩ := hm.2.2.1
    exact Or.inl ⟨(coreImageQuotientEquiv h).trans e⟩
  · obtain ⟨e⟩ := hm.2.2.1
    exact Or.inr ⟨(coreImageQuotientEquiv h).trans e⟩

/-- The image in the source comparison is normalized by the same B image. -/
theorem first_image_normalized :
    coreImage j.J (borelIntersection s d j) ≤
      normalizer (coreImage j.J d.K1 : Set (j.J ⧸ pCore 2 j.J)) :=
  coreImage_normalizes j.intersection_normalizes_first

/-- K₁ lies in the original B in the contained branch. -/
theorem first_le_intersection (h : d.K1 ≤ j.J) :
    d.K1 ≤ borelIntersection s d j := by
  rw [contained_intersection s d j h]
  exact le_inf h d.first_le

/-- Hence its literal quotient image lies in the B image. -/
theorem first_image_le_intersection (h : d.K1 ≤ j.J) :
    coreImage j.J d.K1 ≤ coreImage j.J (borelIntersection s d j) :=
  map_mono (comap_mono (first_le_intersection s d j h))

/-- Relative normality supplies the core containment required by the marked
natural model. -/
theorem component_core_le_intersection (h : d.K1 ≤ j.J) :
    pCore 2 j.J ≤ (borelIntersection s d j).subgroupOf j.J := by
  let := relative_normal d j h
  have hQR := ChapterC.C27Source.source_joinCore_le_radical (contained_input s d j h)
  have hn : j.J ⊔ Mc.pCoreIn 2 ≤ normalizer (j.J : Set G) :=
    sup_le j.J.le_normalizer (radical_normalizes s d j h)
  have hJQ : j.J.pCoreIn 2 ≤ Mc.pCoreIn 2 :=
    (pCoreIn_mono_of_normalizes le_sup_left hn).trans hQR
  intro x hx
  rw [mem_subgroupOf,contained_intersection s d j h]
  exact ⟨x.property,pCoreIn_le 2 Mc (hJQ (mem_map_of_mem j.J.subtype hx))⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison
