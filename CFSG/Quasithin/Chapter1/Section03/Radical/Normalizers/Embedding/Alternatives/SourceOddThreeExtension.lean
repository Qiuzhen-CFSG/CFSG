module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionSigned
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.MarkedImage
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.SourceOddThreeCore

/-!
# The complete original-source odd ternary A.3.12 branch

Restrict the original quotient Sylow to its actual containing component.
The signed ternary theorem constructs an elementary kernel of order q² and
an SL₂(q) quotient, and excludes the unitary sign. Transporting along the
literal subgroup-of equivalence gives case (10) for the original quotient
images. All original KnownSimple and SourceData hypotheses are preserved;
no source data are invented on a central cover.

Source: Aschbacher--Smith A.3.12,A.3.21 and Proposition1.3.8,
printed pp.47--48,55--56,512--514.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
open Section02 Section02.LocalModels
open CFSG.Quasithin.ChapterA.Section03
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Both signed special and projective models of the actual containing image
produce the genuine marked case-(10) embedding. -/
theorem SourceData.odd_ternary_embedding
    {p q : ℕ} (hq : q.Prime) (ho : Odd q)
    {L : Subgroup G} {T : Sylow 2 G}
    {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData KnownSimple.IsKnownSimple p 5 L T C K)
    (unitary : Bool)
    (hm : let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
      let D := quotientImage K N
      IsPSLSign D unitary 3 q ∨ IsSLSign D unitary 3 q) :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    let B := quotientImage (normalizerResidual L (radicalCore p L T)) N
    let D := quotientImage K N
    A312Embedding B D := by
  let : Fact q.Prime := ⟨hq⟩
  let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
  let B := quotientImage (normalizerResidual L (radicalCore p L T)) N
  let D := quotientImage K N
  obtain ⟨Tbar,hTbar,hl,hTB,hBD,hn,_,hD⟩ := h.marked_image_setup
  obtain ⟨S,hS,hlS,hnS⟩ := SourceEmbeddings.exists_local_sylow_normalizing
    Tbar hl hD.subnormal hBD.le hTB
  let e : B.subgroupOf D ≃* B := subgroupOfEquivOfLe hBD.le
  have hn' : ¬ IsQuasisimple ((B.subgroupOf D) ⧸ pCore 2 (B.subgroupOf D)) := by
    intro hh
    let := hh
    exact hn (IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)))
  have hDQ : IsSQTK KnownSimple.IsKnownSimple D :=
    (characteristic_normalizer_quotient_sqtk h.ambient p L T C h.nontrivial).subgroup D
  obtain ⟨hlarge,hsign,_,hext⟩ := SourceEmbeddings.odd_three_local_signed_extension
    hDQ ho S hlS hnS hn' unitary hm
  have hsmall : HasExtension B (ElementaryModel q 2) (fun X _ => IsSL X 2 q) := by
    obtain ⟨U,hUN,hU,F,_,_,hF,⟨eQ⟩⟩ := hext
    let V := U.map e.toMonoidHom
    let : V.Normal := hUN.map e.toMonoidHom e.surjective
    let eU := U.equivMapOfInjective e.toMonoidHom e.injective
    let ep := QuotientGroup.congr U V e rfl
    exact ⟨V,inferInstance,⟨eU.symm.trans hU.some⟩,F,inferInstance,inferInstance,hF,
      ⟨ep.symm.trans eQ⟩⟩
  subst unitary
  exact A312Embedding.ten q hq ho hlarge hsmall hm

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
