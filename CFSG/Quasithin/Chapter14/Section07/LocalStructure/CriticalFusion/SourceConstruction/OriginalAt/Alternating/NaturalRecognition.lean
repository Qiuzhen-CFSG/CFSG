module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NaturalRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.IrreducibleQuotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.IrreducibleQuotient
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.FieldFour
public import Theory.Representation.AlternatingFiveTwists.SymmetricExtension

/-!
# Natural recognition from the local alternating residual

Apply the proved binary A₅ classification to the literal irreducible fixed quotient. Extend and exclude the deleted case over the same S₅ marking. Transport the entire action in the natural case, retaining the exact K-fixed kernel. The source-data application discharges recognition and alternating uniqueness; residual alternatives and independent G₂ exclusion remain explicit.

Only Structural1222At at the original G,T is used. Independent model and
section lemmas are reused from LocalReduction; its universal APIs are preserved.
Source: Aschbacher–Smith, final paragraph of 14.7.40, printed p.1063,
and 14.7.52–63, printed pp.1065–1069. Earlier structural source discharge
and the unconditional classification remain with their existing owners.
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
theorem naturalRecognition_of_alternating_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hAlt : AlternatingResidual F) : NaturalRecognition F := by
  intro W _ _ ρ s
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨e,σ,hσ,hi,hf,hI,p,hp,hk⟩ :=
    exists_faithful_irreducible_fixed_quotient_at h hab structural hAlt s
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
    exact (no_deleted_quotient_at h structural e s q (D.surjective.comp hp)).elim

/-- The source constructor now needs only the residual alternatives and the
separately owned G₂ exclusion, besides the genuine earlier structural input. -/
theorem exists_data_of_residual_alternatives_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (h52 : AlternatingResidual F ∨ G2Residual F) (h53 : ¬ G2Residual F) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) := by
  exact exists_data_of_recognition_branches_at d h hab structural h52 h53
    (naturalRecognition_of_alternating_at h hab structural)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
