module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointSolvable
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.OffenderSubgroup
public import Theory.GroupTheory.NormalSymmetricThreeMarked
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# B.5 on the original paired-point span

The second local residual is two-perfect, normalized by the original common
Sylow subgroup, and has order dividing three times a power of two. If the
normal offender subgroup were symmetric-three, that residual image would
centralize it or be its cubic residual. The first case contradicts the
original Thompson movement. The second makes the residual image normal;
its moved space then has more than four elements by the literal full-span
calculation, whereas the symmetric-three source module has dimension two.

The complete corrected B.5 theorem therefore gives four remaining cases on
the actual restricted point-span action. Its SQTK cover is the original
point join with its literal centralizer kernel. SourceAssembly/PointOffender
uses the result after every original Sylow rechoice.

Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.3--6, pp.103--110.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The actual paired-point offender action cannot be the S₃ source case. -/
theorem point_offender_not_symmetricThree
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁)
    (hPv : P₁ ≤ Gv (markedV d.flag.flag.module))
    (hinter : P₁ ⊓ (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)) =
      ChapterB.baumann (T : Subgroup G)) :
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let J := P₁ ⊔ P₂
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    P₁.pCoreIn 2 ≠ P₂.pCoreIn 2 →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let W := conjugateSpanBy (zpowers x) ⊤
      IsFFModule (ChapterB.InternalThompsonAction.action W) →
      ¬ Nonempty (ChapterB.SourceInduction.SymmetricThreeCase
        ((ChapterB.InternalThompsonAction.action W).comp
          (offenderSubgroup (ChapterB.InternalThompsonAction.action W)).subtype)) := by
  intro P₂ J hg hne x hx hr
  let := hr.normal
  let := hr.elementary
  intro W hff hcase
  let f := QuotientGroup.mk' (centralizer (W : Set J))
  obtain ⟨c⟩ := hcase
  let K := (Lv L (markedV d.flag.flag.module)).subgroupOf J
  let ρ := ChapterB.InternalThompsonAction.action W
  let N := offenderSubgroup ρ
  let : N.Normal := offenderSubgroup_normal ρ
  have hBJ : ChapterB.baumann (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_right
  have hKJ : Lv L (markedV d.flag.flag.module) ≤ J := le_sup_left.trans le_sup_right
  have hJv : J ≤ Gv (markedV d.flag.flag.module) := sup_le hPv (sup_le
    ((map_subtype_le _).trans inf_le_right)
    ((source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem).le.trans inf_le_right))
  obtain ⟨S,hS⟩ := (point_baumann_sylow d hH hB hZ hs hz).restrict hBJ hJv
  have hSK : (S : Subgroup J) ≤ normalizer (K : Set J) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro k
    exact mem_normalizer_iff.mp (point_residual_normalized_by_baumann d hH hB hZ hs hz
      (hS ▸ mem_map_of_mem J.subtype ht)) (k:G)
  have hp : IsPPerfect 2 K := (isPPerfect_embedded_pResidual 2
    (L ⊓ Gv (markedV d.flag.flag.module))).of_surjective
      (subgroupOfEquivOfLe hKJ).symm.toMonoidHom (subgroupOfEquivOfLe hKJ).symm.surjective
  have hpimage : IsPPerfect 2 (K.map f) := hp.of_surjective
    (f.subgroupMap K) (f.subgroupMap_surjective K)
  have hcard : ∃ n, Nat.card (K.map f) ∣ 3 * 2 ^ n := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := Lv L (markedV d.flag.flag.module))).exists_card_eq
    have hc := card_eq_card_quotient_mul_card_subgroup (pCore 2 (Lv L (markedV d.flag.flag.module)))
    rw [d.flag.flag.residualQuotient_card,hn] at hc
    refine ⟨n,?_⟩
    have hh := card_map_dvd (f := f) (H := K)
    rw [Nat.card_congr (subgroupOfEquivOfLe hKJ).toEquiv,hc] at hh
    exact hh
  have hm := point_residual_image_offenders_move d hH hB hZ hs hz hBJ hKJ hJv x hx hr
  obtain he | he := NormalSymmetricThreeMarked.eq_residual_or_centralizes_of_card_dvd
    N c.equiv (S.mapSurjective (QuotientGroup.mk'_surjective _)) (K.map f) hpimage
    ((map_mono hSK).trans (K.le_normalizer_map f)) hcard
  · have hn : (K.map f).Normal := by rw [he]; infer_instance
    have hlarge := (point_moved_support_gt_four_of_normal_image d hH hB hZ hs hz
      horiginal hPv hinter hg hne x hx hr hn).2
    have hKN : K.map f ≤ N := he ▸ map_subtype_le _
    have hle : subspaceCommutator ρ ⊤ (K.map f) ≤ subspaceCommutator ρ ⊤ N := by
      apply Submodule.span_mono
      rintro _ ⟨g,hg,v,hv,rfl⟩
      exact ⟨g,hKN hg,v,hv,rfl⟩
    have hdim : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ N) = 2 := by
      have hh := c.dimension
      change Module.finrank (ZMod 2)
        (subspaceCommutator (ρ.comp N.subtype) ⊤ ⊤) = 2 at hh
      rwa [subspaceCommutator_comp_map,←MonoidHom.range_eq_map,range_subtype] at hh
    have hsmall : Nat.card (subspaceCommutator ρ ⊤ (K.map f)) ≤ 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      exact (Nat.pow_le_pow_right (by decide : 0 < 2)
        ((Submodule.finrank_mono hle).trans_eq hdim)).trans_eq rfl
    exact (not_lt_of_ge hsmall) hlarge
  · exact hm (le_centralizer_iff.mp he)


/-- Complete B.5 on the literal offender action, with the S₃ case excluded. -/
theorem point_offender_source_alternatives
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁)
    (hPv : P₁ ≤ Gv (markedV d.flag.flag.module))
    (hinter : P₁ ⊓ (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)) =
      ChapterB.baumann (T : Subgroup G)) :
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let J := P₁ ⊔ P₂
    IsSQTK KnownSimple.IsKnownSimple J →
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    P₁.pCoreIn 2 ≠ P₂.pCoreIn 2 →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let W := conjugateSpanBy (zpowers x) ⊤
      IsFFModule (ChapterB.InternalThompsonAction.action W) →
      let ρ := ChapterB.InternalThompsonAction.action W
      let N := offenderSubgroup ρ
      let σ := ρ.comp N.subtype
      (IsQuasisimple (generalizedFitting N) ∧
        Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
          σ (generalizedFitting N))) ∨
      Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase σ) ∨
      Nonempty (ChapterB.OuterSixThreeShape N) ∨
      Nonempty (ChapterB.SourceInduction.HyperplaneCase σ) := by
  intro P₂ J hSQ hg hne x hx hr
  let := hr.normal
  let := hr.elementary
  intro W hff ρ N σ
  let f := QuotientGroup.mk' (centralizer (W : Set J))
  let cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      (J ⧸ centralizer (W : Set J)) := {
    Cover := J
    kernel := centralizer (W : Set J)
    sqtk := hSQ
    equiv := MulEquiv.refl _ }
  have hf : Function.Injective ρ := NormalElementaryQuotient.representation_injective W f
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hclass := ChapterB.SourceInduction.offenderSubgroup_adequateAlternative ρ hf
    hr.quotient_pCore_eq_bot cover
  obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
  have hffN : IsFFModule σ :=
    ⟨A.subgroupOf N,(hA.isOffender ρ).subgroupOf ρ (hA.le_offenderSubgroup ρ)⟩
  cases hclass.of_ff σ hffN with
  | quasisimple hq c => exact Or.inl ⟨hq,⟨c⟩⟩
  | symmetricThree c =>
    exact (point_offender_not_symmetricThree d hH hB hZ hs hz horiginal hPv hinter
      hg hne x hx hr hff ⟨c⟩).elim
  | twoFactors c => exact Or.inr (Or.inl ⟨c⟩)
  | outerSixThree c => exact Or.inr (Or.inr (Or.inl ⟨c⟩))
  | hyperplane c => exact Or.inr (Or.inr (Or.inr ⟨c⟩))

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
