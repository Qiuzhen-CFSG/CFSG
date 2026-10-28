module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourAlphaNativeSource
public import Theory.GroupTheory.Amalgam.SylowRigidity

/-!
# Native J₂ Borel glue for DGS field four

The two endpoint maps are independently aligned on the literal native Borel.
Their discrepancy is recorded as a single overlap twist; an extension of that
automorphism along the native Borel inclusion removes the twist.

Source: DGS, Groups and Graphs (1985), (10.9), pp.162--163.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open Theory.GroupTheory
open SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance glueFieldFourAlphaNativeAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2


local notation "Jα" => Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.p₂
local notation "JQ" => Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.q₂
local notation "JS" => Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.s
local notation "JB" => Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap.B

/-- Both native Borel squares give one compatible comparison with a single
explicit twist of the right overlap map. -/
theorem original_bTwo_field_four_reduced_twist_iso
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    ∃ d : MulAut GreenBook.HallJanko.j2Model.toMarking.B,
      Nonempty (RankTwoAmalgam.Iso
        (OriginalExtension.reducedAmalgam L S).reverse
        (RankTwoAmalgam.twistRight GreenBook.HallJanko.j2Model.toMarking.amalgam d)) := by
  obtain ⟨fα,fBα,fTα,fQα,hBα,hTα,hQα⟩ :=
    original_bTwo_field_four_reduced_alpha_borel_equiv
      h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨fβ,fBβ,fTβ,hBβ,hTβ,dβ,hdβ⟩ :=
    original_bTwo_field_four_reduced_beta_borel_equiv
      h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  let fL := ((MulEquiv.subgroupCongr (P₀_eq_source h 1).symm).trans fβ).trans
    (MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_P_zero.symm)
  let fR := ((MulEquiv.subgroupCongr (P₀_eq_source h 0).symm).trans fα).trans
    (MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_P_one.symm)
  let fB := ((MulEquiv.subgroupCongr (B₀_eq_source h).symm).trans fBβ).trans
    (MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_B.symm)
  let gB := ((MulEquiv.subgroupCongr (B₀_eq_source h).symm).trans fBα).trans
    (MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_B.symm)
  refine ⟨fB.symm.trans gB, ⟨{
    left := fL
    middle := fB
    right := fR
    left_commutes := ?_
    right_commutes := ?_ }⟩⟩
  · intro b
    apply Subtype.ext
    exact (hBβ ((MulEquiv.subgroupCongr (B₀_eq_source h).symm) b)).symm
  · intro b
    change fR ((OriginalExtension.reducedAmalgam L S).reverse.right b) =
      GreenBook.HallJanko.j2Model.toMarking.amalgam.right (gB (fB.symm (fB b)))
    rw [fB.symm_apply_apply]
    apply Subtype.ext
    exact (hBα ((MulEquiv.subgroupCongr (B₀_eq_source h).symm) b)).symm

/-- Extending every automorphism of the literal native Borel to the second
endpoint removes the only remaining discrepancy between the source squares. -/
theorem original_bTwo_field_four_reduced_iso_of_borel_extensions
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4)
    (hExt : ∀ d : MulAut JB, RankTwoAmalgam.ExtendsAcross
      (Subgroup.inclusion Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap.B_le_p₂) d) :
    Nonempty (RankTwoAmalgam.Iso
      (OriginalExtension.reducedAmalgam L S).reverse
      GreenBook.HallJanko.j2Model.toMarking.amalgam) := by
  obtain ⟨d, ⟨f⟩⟩ := original_bTwo_field_four_reduced_twist_iso
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  let eB := MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_B
  let eR := MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_P_one
  obtain ⟨a,ha⟩ := hExt (eB.symm.trans (d.symm.trans eB))
  have hright : RankTwoAmalgam.ExtendsAcross
      GreenBook.HallJanko.j2Model.toMarking.amalgam.right d.symm := by
    refine ⟨eR.trans (a.trans eR.symm), ?_⟩
    intro b
    have hsq (b : GreenBook.HallJanko.j2Model.toMarking.B) :
        (Subgroup.inclusion
          Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap.B_le_p₂)
          (eB b) = eR (GreenBook.HallJanko.j2Model.toMarking.amalgam.right b) := by
      rfl
    apply eR.injective
    change a (eR (GreenBook.HallJanko.j2Model.toMarking.amalgam.right b)) =
      eR (GreenBook.HallJanko.j2Model.toMarking.amalgam.right (d.symm b))
    rw [← hsq b, ← hsq (d.symm b)]
    simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using ha (eB b)
  have hfactor : RankTwoAmalgam.FactorsThrough
      GreenBook.HallJanko.j2Model.toMarking.amalgam d := by
    refine ⟨MulEquiv.refl _, d.symm, ?_, hright, ?_⟩
    · exact ⟨MulEquiv.refl _, fun _ => rfl⟩
    · ext b
      rfl
  exact ⟨f.trans hfactor.iso⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
