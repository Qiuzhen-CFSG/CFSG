module
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.BinaryFour
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.BinaryFiveSource
public import Theory.Representation.SmallDisplacementParabolics.Models
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.AutomorphismModel.Structure
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient

/-!
# Recognition when the inner binary component is irreducible

For Aut(L₄(2)) and Aut(L₅(2)), the actual inner subgroup is quasisimple
of index two. Faithful binary irreducibility kills the two-core, so it is
also the generalized Fitting subgroup. The proved cubic degree sieves
apply to this literal component. The natural dimension is too small for
a faithful action of the full automorphism group. The degree-ten exterior
action is self-normalizing and cannot extend to that group. The remaining
orthogonal-six restriction extends to the actual deleted S₈ action.

This proves the irreducible-inner branch of the partner-chief recognition
used in 15.2.27(2), printed p.1119. The reducible restriction remains a
separate branch; no irreducibility of that restriction is inferred from
ambient irreducibility.
-/

public section
open Subgroup Representation Theory.GroupTheory
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits.AutomorphismModel
open CFSG CFSG.Quasithin
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem no_faithful_natural_degree {n : ℕ} (hn : n = 4 ∨ n = 5)
    (ρ : Representation (ZMod 2) (MulAut (LinearGroup n)) W)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) W = n) : False := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  let f : W ≃ₗ[ZMod 2] Space n := LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hd)
  let φ := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space n)).toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv f).toMonoidHom.comp ρ.asGroupHom)
  have hi : Function.Injective φ := by
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space n)).injective.comp
    apply (LinearMap.GeneralLinearGroup.congrLinearEquiv f).injective.comp
    intro x y h
    exact hf (congrArg Units.val h)
  have hle := Nat.card_le_card_of_injective φ hi
  change Nat.card (MulAut (LinearGroup n)) ≤ Nat.card (LinearGroup n) at hle
  have he := (MulAut.innerSubgroup (LinearGroup n)).index_mul_card
  rw [inner_index hn, ← Nat.card_congr (innerEquiv (by omega : 0 < n)).toEquiv] at he
  have hpos : 0 < Nat.card (LinearGroup n) := Nat.card_pos
  omega

theorem irreducible_inner_model {n : ℕ} (hn : n = 4 ∨ n = 5)
    (ρ : Representation (ZMod 2) (MulAut (LinearGroup n)) W)
    [IsIrreducible ρ]
    (hsq : IsSQTK KnownSimple.IsKnownSimple (MulAut (LinearGroup n)))
    (hf : Function.Injective ρ)
    (hq : BinaryOffender.quadraticRatio ρ ≤ 2)
    (hi : IsIrreducible (ρ.comp (MulAut.innerSubgroup (LinearGroup n)).subtype)) :
    SmallDisplacementParabolics.ActionModel ρ := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  let I := MulAut.innerSubgroup (LinearGroup n)
  let : IsQuasisimple I := (inner_isComponent (by omega : 3 ≤ n)).2
  have hcore : pCore 2 (MulAut (LinearGroup n)) = ⊥ := by
    have hle := normal_p_subgroup_le_ker ρ (pCore 2 _) pCore_isPGroup
    rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hf] at hle
    exact bot_unique hle
  have hp : IsPGroup 2 (MulAut (LinearGroup n) ⧸ I) := by
    apply isPGroup_iff_card_dvd_pow.mpr
    refine ⟨1, ?_⟩
    change I.index ∣ 2 ^ 1
    rw [inner_index hn]
    decide
  have h : ChapterK.RankOne.SourceHypotheses ρ I :=
    ⟨hsq,generalizedFitting_eq_of_quasisimple_two_quotient I hp hcore,
      inferInstance,hf,hi,(BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq⟩
  have h' : ChapterK.Linear.Recognition.SourceHypothesis KnownSimple.IsKnownSimple ρ I :=
    ⟨inferInstance,inferInstance,hsq,h.fitting,h.quasisimple,hf,hi,h.smallCubic⟩
  let e : I ≃* SL(n,ZMod 2) := (innerEquiv (by omega : 0 < n)).symm.trans
    (slEquivLinear n).symm
  have hproper : I ≠ ⊤ := by
    intro he
    have hi := inner_index hn
    change I.index = 2 at hi
    rw [he,index_top] at hi
    contradiction
  rcases hn with rfl | rfl
  · rcases ChapterK.Linear.Recognition.BinaryCubicSieve.four_small_modules h' e with hd | ho
    · exact (no_faithful_natural_degree (Or.inl rfl) ρ hf hd).elim
    let a := ho
    obtain ⟨j,f,hf'⟩ := a
    let d := Atlas.Order20160A8.DeletedEight.splitEquiv.trans
      ChapterK.Linear.OrthogonalSix.deletedEightEquivNatural
    let E : ChapterB.QuasisimpleSource.ActionEquiv (ρ.comp I.subtype)
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) := {
      groupEquiv := j
      linearEquiv := f.trans d
      intertwines := by
        intro g v
        change d (f (ρ g v)) = _
        rw [show f (ρ g v) = _ from hf' g v]
        change ChapterK.Linear.OrthogonalSix.deletedEightEquivNatural
          (Atlas.Order20160A8.DeletedEight.splitEquiv
            (Atlas.Order20160A8.DeletedEight.splitEquiv.symm
              (Atlas.Order20160A8.DeletedEight.quotientPerm (j g).val
                (Atlas.Order20160A8.DeletedEight.splitEquiv (f v))))) = _
        rw [LinearEquiv.apply_symm_apply]
        exact ChapterK.Linear.OrthogonalSix.deletedEightEquivNatural_intertwines _ _ }
    obtain ⟨_,⟨a⟩⟩ := (ChapterK.Linear.OrthogonalSix.extension_alternatives ρ I hf E).resolve_left hproper
    let j := Subgroup.topEquiv.symm.trans a.action.groupEquiv
    refine Or.inl ⟨j,⟨Representation.Equiv.mk a.action.linearEquiv ?_⟩⟩
    intro g
    apply LinearMap.ext
    intro v
    exact a.action.intertwines ⟨g,mem_top g⟩ v
  · rcases ChapterK.Linear.Recognition.BinaryCubicSieve.five_degrees h' e with hd | hd
    · exact (no_faithful_natural_degree (Or.inr rfl) ρ hf hd).elim
    obtain ⟨a⟩ := ChapterK.Linear.Exterior.SourceFF.exteriorAction_of_finrank h' e hd
    exact (hproper (ChapterK.Linear.Exterior.SourceFF.whole_of_exterior h' a)).elim

end CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition
