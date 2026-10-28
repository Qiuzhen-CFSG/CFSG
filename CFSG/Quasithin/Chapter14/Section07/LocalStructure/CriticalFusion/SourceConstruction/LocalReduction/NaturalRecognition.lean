module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.IrreducibleQuotient
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.FieldFour
public import Theory.Representation.AlternatingFiveTwists.SymmetricExtension

/-!
# Natural recognition from the original alternating residual

The literal fixed quotient of U/V₁ is an irreducible A₅ module and still
carries the faithful full S₅ action. The genuine binary A₅ classification
identifies it with either the natural SL₂(4) module or the deleted
five-point module. In the latter case the intertwiner extends over the
same full S₅ marking, and its composite with the original quotient map
contradicts seed separation. In the natural case transporting the entire
S₅ action gives the required natural quotient with exactly the K-fixed
kernel. The additive comparison retains the binary module structure used
by Chapter J's concrete four-space.

The final application constructs source Data from the residual alternatives
and the independent G₂ exclusion, with no module-recognition callback or
Sylow fixed-index premise. The residual alternatives themselves, including
the larger-field reduction of 14.7.40, remain to be proved.

Source: Aschbacher–Smith, final argument of 14.7.40, printed p.1063,
and the source-data application in 14.7.63, printed p.1069.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "A5" => alternatingGroup (Fin 5)

/-- Natural recognition on the original section follows from the actual
irreducible alternatives, after extending and excluding the deleted action. -/
theorem naturalRecognition_of_alternating
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hAlt : AlternatingResidual F) : NaturalRecognition F := by
  intro W _ _ ρ s
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨e,σ,hσ,hi,hf,hI,p,hp,hk⟩ :=
    exists_faithful_irreducible_fixed_quotient h hab structural hAlt s
  let C := (fixedSubrepresentation σ A5).toSubmodule
  let Q := fixedQuotient σ A5
  let τ := Q.comp ((A5).subtype.comp SL2FourNatural.alternatingFiveEquiv.toMonoidHom)
  let : IsIrreducible (Q.comp (A5).subtype) := hI
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff SL2FourNatural.alternatingFiveEquiv.toMonoidHom
      SL2FourNatural.alternatingFiveEquiv.surjective (Q.comp (A5).subtype)).mpr hI
  have hτ : Function.Injective τ := hf.comp
    ((A5).subtype_injective.comp SL2FourNatural.alternatingFiveEquiv.injective)
  let : Nontrivial SL2FourNatural.SL := SL2FourNatural.alternatingFiveEquiv.symm.injective.nontrivial
  have hn : ∃ a, τ a ≠ 1 := by
    obtain ⟨a,ha⟩ := exists_ne (1 : SL2FourNatural.SL)
    exact ⟨a,fun hh => ha (hτ (hh.trans τ.map_one.symm))⟩
  obtain ⟨_,hnat | hdel⟩ :=
    ChapterG.Section09.DefiningCharacteristic.binary_card_four_action_alternatives τ
      (by rw [Nat.card_eq_fintype_card,SL2FourNatural.card_field]) hn
  · obtain ⟨E⟩ := hnat
    let Eadd : (W ⧸ C) ≃+ ChapterJ.FourSpace := by
      letI : Module (ZMod 2) SL2FourNatural.F := @Algebra.toModule (ZMod 2) SL2FourNatural.F _ _ (ZMod.algebra SL2FourNatural.F 2)
      exact E.toLinearEquiv.toAddEquiv
    let E' : (W ⧸ C) ≃ₗ[ZMod 2] ChapterJ.FourSpace :=
      LinearEquiv.ofBijective (Eadd.toAddMonoidHom.toZModLinearMap 2) Eadd.bijective
    have hE' (g : SL2FourNatural.SL) (w : W ⧸ C) :
        E' (Q (SL2FourNatural.alternatingFiveEquiv g) w) = SL2FourNatural.action g (E' w) := by
      let : Module (ZMod 2) SL2FourNatural.F := @Algebra.toModule (ZMod 2) SL2FourNatural.F _ _ (ZMod.algebra SL2FourNatural.F 2)
      exact LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' g) w
    let a : ChapterJ.L2FourAction := {
      action := E'.conjRingEquiv.toMonoidHom.comp Q
      marking := SL2FourNatural.alternatingFiveEquiv
      restriction := by
        intro g v
        obtain ⟨w,rfl⟩ := E'.surjective v
        change E' (Q (SL2FourNatural.alternatingFiveEquiv g)
          (E'.symm (E' w))) = SL2FourNatural.action g (E' w)
        rw [E'.symm_apply_apply]
        exact hE' g w }
    let q : ρ.IntertwiningMap (a.action.comp (quotientMarking e)) := {
      toLinearMap := E'.toLinearMap.comp p.toLinearMap
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro w
        change E' (p (ρ g w)) = E' (Q (quotientMarking e g) (E'.symm (E' (p w))))
        rw [E'.symm_apply_apply,p.isIntertwining]
        rfl }
    refine ⟨e,a,q,E'.surjective.comp hp,?_⟩
    change (E'.toLinearMap.comp p.toLinearMap).ker = _
    rw [LinearMap.ker_comp_of_ker_eq_bot _ E'.ker,hk]
  · obtain ⟨f,⟨E⟩⟩ := hdel
    let f' := SL2FourNatural.alternatingFiveEquiv.symm.trans f
    have hE (b : A5) (w : W ⧸ C) :
        E (Q b.val w) = BinaryPermutation.naturalRepresentation (Fin 5) (f' b).val (E w) := by
      have hh := LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining'
        (SL2FourNatural.alternatingFiveEquiv.symm b)) w
      change E (Q (SL2FourNatural.alternatingFiveEquiv
        (SL2FourNatural.alternatingFiveEquiv.symm b)) w) =
          BinaryPermutation.naturalRepresentation (Fin 5) (f' b).val (E w) at hh
      simpa only [MulEquiv.apply_symm_apply] using hh
    obtain ⟨D,hD⟩ := AlternatingFiveTwists.symmetric_deleted_equiv Q hf f' E.toLinearEquiv hE
    let q : ρ.IntertwiningMap
        ((BinaryPermutation.coreRepresentation (Fin 5)).comp (quotientMarking e)) := {
      toLinearMap := D.toLinearMap.comp p.toLinearMap
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro w
        change D (p (ρ g w)) = _
        rw [p.isIntertwining]
        exact hD (quotientMarking e g) (p w) }
    exact (no_deleted_quotient h structural e s q (D.surjective.comp hp)).elim

/-- The source constructor now needs only the residual alternatives and the
separately owned G₂ exclusion, besides the genuine earlier structural input. -/
theorem exists_data_of_residual_alternatives
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (h52 : AlternatingResidual F ∨ G2Residual F) (h53 : ¬ G2Residual F) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) := by
  exact exists_data_of_recognition_branches d h hab structural h52 h53
    (naturalRecognition_of_alternating h hab structural)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
