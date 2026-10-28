module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramCentralCoreActor
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramCoreModel
public import Theory.SpecificGroups.PSL3.BinaryOddCenterCover.FullTorusFixer
import all CFSG.Quasithin.Chapter14.Section02.NormalKOne

/-!
# Excluding the cubic cover in the original exceptional diagram branch

A two-core actor failing to normalize the selected point-parabolic
residual moves the diagram, fixes the whole torus quotient, and fixes
the component quotient's odd center pointwise. The finite SL₃(4) cover
calculation therefore kills that center. The original perfect central
cover becomes the actual PSL₃(4) isomorphism, with its source map retained.

Source: Aschbacher--Smith 14.2.12(1), printed p.984.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE ChapterE.Structure
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

 theorem original_linear_cover_equiv_of_core_not_normalized
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    [K.Normal] (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    (e : sourceImage (ChapterB.minimalParabolicMax T hP) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap (ChapterB.minimalParabolicMax T hP) K).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F)
    (hfail : ¬ (ChapterB.minimalParabolicMax T hP).pCoreIn 2 ≤
      normalizer (markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e
        (Matrix.PSL3.LinearThree.pointParabolic F) : Set H)) :
    Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := by
  let M := ChapterB.minimalParabolicMax T hP
  let Q := K ⧸ pCore 2 K
  let := hqK
  let : IsSimpleGroup (sourceImage M K) :=
    (source_component_simple_image T hP hs K hK hgen).1
  let : IsQuasisimple (sourceImage M K) :=
    (source_component_simple_image T hP hs K hK hgen).2.1.2
  let c := originalComponentStarCover T hP hs K hK hqK hgen
  let f := e.toMonoidHom.comp c.toMonoidHom
  have hf : Function.Surjective f := e.surjective.comp c.surjective
  have hk : f.ker = center Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact c.toCovering.ker_eq_center_of_isSimple
  let d : Q ⧸ center Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hd (x : Q) : d (QuotientGroup.mk x) = f x := rfl
  have hmap (x : K) : f (QuotientGroup.mk' (pCore 2 K) x) = markedParabolicMap M K e x := rfl
  have ho : Odd (Nat.card (center Q)) := Nat.not_even_iff_odd.mp (by
    rw [even_iff_two_dvd]
    exact PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) _ le_rfl)
  obtain ⟨g,hg,hn⟩ := Set.not_subset.mp hfail
  let α := normalQuotientAction K (pCore 2 K) g
  let β := markedParabolicActor M K e g
  have hcomm (x : Q) : β (d (QuotientGroup.mk x)) = d (QuotientGroup.mk (α x)) := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
    rw [hd,normalQuotientAction_apply_mk,hd,hmap,hmap]
    exact markedParabolicActor_apply M K e g x
  have hcenter : ∀ z ∈ center Q, α z = z :=
    original_core_actor_fixes_quotient_center T hP hs K hK hqK hgen e g hg
  have hB := markedParabolicActor_borel M K e he g (pCoreIn_le 2 M hg)
  have hfix (b : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
      (hb : b ∈ Matrix.PSL3.CartanActions.torus F) :
      β b * b⁻¹ ∈ Matrix.PSL3.LinearThree.unipotent F := by
    have hh := markedParabolicActor_core_displacement M K e he g hg b
      (Matrix.PSL3.CartanActions.torus_le_borel F hb)
    rwa [pCoreIn,Matrix.PSL3.CartanActions.BorelQuotient.twoCore_eq F
      (n := 2) (by simpa using hF),
      map_subgroupOf_eq_of_le (Matrix.PSL3.LinearThree.unipotent_le_borel F)] at hh
  have hmove : ¬ (Matrix.PSL3.LinearThree.OuterExtensions.PreservesPointType F β ∧
      Matrix.PSL3.LinearThree.OuterExtensions.PreservesLineType F β) := by
    rintro ⟨⟨u,hu⟩,_⟩
    apply hn
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply markedParabolicResidual_conj M K e _ _ g
    rcases Matrix.PSL3.LinearThree.point_parabolic_map_pair_of_borel F β hB with hp | hp
    · exact hp
    · exact (Matrix.PSL3.LinearThree.OuterExtensions.pointParabolic_not_conjugate_line
        F (n := 2) (by decide) (by simpa using hF) u (hu.symm.trans hp)).elim
  have hz := Matrix.PSL3.BinaryOddCenterCover.FullTorusFixer.center_eq_bot_of_diagram_moving_torus_fixer
    hF d ho α β hcomm hcenter hB hfix hmove
  have hi : Function.Injective f := f.ker_eq_bot_iff.mp (hk.trans hz)
  exact ⟨MulEquiv.ofBijective f ⟨hi,hf⟩⟩

end CFSG.Quasithin.Chapter14.Section02
