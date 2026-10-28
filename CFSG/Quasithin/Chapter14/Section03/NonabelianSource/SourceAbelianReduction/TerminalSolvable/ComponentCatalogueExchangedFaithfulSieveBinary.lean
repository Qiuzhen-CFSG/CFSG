module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSieveBounds
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition
public import Theory.Representation.BinaryQuadraticConstituent

/-!
# Excluding the larger binary linear models on the exchanged orbit

Properness rules out every full binary linear group in its natural degree,
by the faithful action's order. The proved small-module alternatives for
PSL₄(2) leave an orthogonal action; its preserved quadratic form pulls back
to a nonzero invariant form on the same H-module, contradicting its
non-self-duality. For PSL₅(2), the sharp automorphism-rank bound excludes
degree ten, so the proved degree gap suffices without exterior-module
recognition. Each exclusion is applied to the literal constituent H image.

Source: Aschbacher--Smith G.9.3(11)--(13) and G.11.6, printed pp.354,366.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace ExchangedFaithfulSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)

include s


/-- The faithful proper orbit action cannot have the full binary linear group's
order in its natural degree. This uses its actual action homomorphism. -/
theorem not_binary_linear_natural_degree {n : ℕ} (hn : 0 < n)
    (e : componentOrbit L ⊤ ≃* PSL(n, ZMod 2))
    (hd : finrank (ZMod 2) I = n) : False := by
  let f : I ≃ₗ[ZMod 2] _root_.BinaryLinear.OuterCyclic.Space n :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let E : (I →ₗ[ZMod 2] I)ˣ ≃* _root_.BinaryLinear.OuterCyclic.LinearGroup n :=
    (Units.mapEquiv f.conjRingEquiv.toMulEquiv).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
        (_root_.BinaryLinear.OuterCyclic.Space n))
  have hc : Nat.card (I →ₗ[ZMod 2] I)ˣ = Nat.card (componentOrbit L ⊤) :=
    (Nat.card_congr E.toEquiv).trans
      (Nat.card_congr (e.trans (_root_.BinaryLinear.OuterCyclic.projectiveEquivLinear hn)).toEquiv).symm
  let : Finite (I →ₗ[ZMod 2] I)ˣ := Finite.of_equiv (componentOrbit L ⊤)
    ((e.trans (_root_.BinaryLinear.OuterCyclic.projectiveEquivLinear hn)).trans E.symm).toEquiv
  let r : componentOrbit L ⊤ →* (I →ₗ[ZMod 2] I)ˣ := s.orbitAction.asGroupHom
  have hi : Function.Injective r := s.faithful_data.1
  exact s.proper (hi.bijective_of_nat_card_le hc.le).2

/-- Both binary PSL₄ module alternatives are impossible: the natural image
is full linear, and the orthogonal image supplies a nonzero invariant form. -/
theorem not_binary_linear_four_equiv
    (e : componentOrbit L ⊤ ≃* PSL(4, ZMod 2)) : False := by
  let σ := s.orbitAction.comp e.symm.toMonoidHom
  have hi : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      s.orbitAction).mpr s.irreducible
  have hf : Function.Injective σ := s.orbit_faithful.comp e.symm.injective
  have hu := s.orbit_degree_le_automorphism_rank_add_two
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := _root_.BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le
  have hd : finrank (ZMod 2) I ≤ 10 := by omega
  rcases ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.small_modules
      σ hf hi hd with hnat | ⟨a,f,hf⟩
  · exact s.not_binary_linear_natural_degree (by decide) e hnat
  · let q := (ClassicalOrthogonal.formD 3 (ZMod 2)).comp f.toLinearMap
    have hq : ∀ h : componentOrbit L ⊤, ∀ v : I, q (s.orbitAction h v) = q v := by
      intro h v
      have hh := hf (e h) v
      change f (s.orbitAction (e.symm (e h)) v) =
        Representation.BinaryLinearRecognition.orthogonalEightAction (a (e h)) (f v) at hh
      rw [e.symm_apply_apply] at hh
      change ClassicalOrthogonal.formD 3 (ZMod 2) (f (s.orbitAction h v)) = _
      rw [hh]
      exact Representation.BinaryLinearRecognition.orthogonalEightAction_preserves_form _ _
    let : IsIrreducible s.orbitAction := s.irreducible
    have hz := BinaryQuadraticConstituent.quadratic_eq_zero_of_not_self_dual s.orbitAction
      (by change 1 < finrank (ZMod 2) I; have := s.dimension_gt_two; omega) q hq s.faithful_data.2.1
    have hval := congrArg (fun q : QuadraticForm (ZMod 2) I => q (f.symm (fun _ => 1))) hz
    change ClassicalOrthogonal.formD 3 (ZMod 2) (f (f.symm (fun _ => 1))) = 0 at hval
    rw [f.apply_symm_apply] at hval
    norm_num [ClassicalOrthogonal.formD_apply, Fin.sum_univ_three] at hval
    exact (by decide : (3 : ZMod 2) ≠ 0) hval

/-- The exhaustive degree gap is sufficient for PSL₅(2); its degree-ten
module identification is not needed for this exchanged source. -/
theorem not_binary_linear_five_equiv
    (e : componentOrbit L ⊤ ≃* PSL(5, ZMod 2)) : False := by
  let E := e.trans Representation.SL5TenDimensional.projectiveEquiv.symm
  let σ := s.orbitAction.comp E.symm.toMonoidHom
  have hi : IsIrreducible σ :=
    (irreducible_comp_surjective_iff E.symm.toMonoidHom E.symm.surjective
      s.orbitAction).mpr s.irreducible
  have hf : Function.Injective σ := s.orbit_faithful.comp E.symm.injective
  have hu := s.orbit_degree_le_automorphism_rank_add_two
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := _root_.BinaryLinear.AutomorphismTwoRank.psl5_two_rank_le
  have hd : finrank (ZMod 2) I ≤ 14 := by omega
  rcases ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.finrank_eq_five_or_ten
      σ hf hi hd with h5 | h10
  · exact s.not_binary_linear_natural_degree (by decide) e h5
  · change finrank (ZMod 2) I = 10 at h10
    omega

/-- The two larger binary linear candidates are excluded on the same H image. -/
theorem image_not_binary_linear_four_or_five :
    ¬ (Nonempty (s.image (componentOrbit L ⊤) ≃* PSL(4, ZMod 2)) ∨
      Nonempty (s.image (componentOrbit L ⊤) ≃* PSL(5, ZMod 2))) := by
  intro h
  rcases h with h | h <;> obtain ⟨e⟩ := h
  · exact s.not_binary_linear_four_equiv (s.orbitEquiv.trans e)
  · exact s.not_binary_linear_five_equiv (s.orbitEquiv.trans e)

end ExchangedFaithfulSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
