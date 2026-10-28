module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeGeometry
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.EvenDegree
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedProperFaithful
public import Theory.Representation.OrthogonalFourPlusMatrix.GaloisComparison
public import Theory.Representation.OrthogonalFourPlusMatrix.AmbientSemilinear
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedCoefficientField
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.ExchangedA5Action

/-!
# Whole marked component pairs and their actual tensor model

Evenness excludes three-dimensional factors. The completed source carrier
restrictions then identify the actual component orbit with the natural
split four-dimensional orthogonal action over a binary extension field.
At degree eight this constructs the genuine ExchangedA5.ActionModel on the
literal dotted T-conjugate span and retains the original invariant form.
The scalar commutant makes the original actor semilinear, so the original
marked coefficient bound forces the field to be GF(4).

Source: Aschbacher–Smith G.9.3(15), G.11.7 and 14.3.15,
printed pp.354–357,366–368,994.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative MatrixGroups
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

open ChapterG.Section09
attribute [local instance] instAlgebraZModGaloisField
/-- Every whole two-component orbit is the actual split orthogonal tensor
on the original terminal space. The field degree remains explicit. -/
theorem whole_pair_recognition (hi : I = ⊤) (hne : componentOrbit L ⊤ ≠ L) :
    ∃ n : ℕ, 1 < n ∧ Module.finrank (ZMod 2) (Additive F.Uhat) = 4*n ∧
      Nonempty (L ≃* SL(2,GaloisField 2 n)) ∧
      Quasiequivalent (F.terminalRepresentation.comp (componentOrbit L ⊤).subtype)
        (TwoComponents.fourOrthogonal n) := by
  have h := s.componentHypothesis_of_whole hi
  rcases h.components with he | ⟨L₂,h₂,hH,hq⟩
  · exact (hne he).elim
  have hne₂ : L ≠ L₂ := by
    intro he
    apply hne
    simpa only [← he,sup_idem] using hH
  apply TwoComponents.even_component_join_recognition h h₂ hH hne₂ hq
  rw [s.actor_dimension]
  exact even_two_mul _

/-- The source coefficient bound forces GF(4) in every whole component pair.
The semilinear homomorphism is constructed from its actual scalar commutant. -/
theorem degree_eight_of_whole_pair (hi : I = ⊤) (hne : componentOrbit L ⊤ ≠ L) :
    Module.finrank (ZMod 2) (Additive F.Uhat) = 8 := by
  obtain ⟨n,hn,hdeg,_,a,c,hc⟩ := s.whole_pair_recognition hi hne
  let k := GaloisField 2 n
  let e := a.trans (ClassicalOrthogonal.FourPlusMatrix.elementaryEquiv (F := k)).symm
  let d := c.trans ((ClassicalOrthogonal.FourPlusMatrix.coordinates (F := k)).restrictScalars (ZMod 2))
  let τ : Representation (ZMod 2) F.TerminalHdot (ClassicalOrthogonal.FourPlusMatrix.Mat (F := k)) :=
    d.conjRingEquiv.toMonoidHom.comp F.terminalRepresentation
  have hτ (l : componentOrbit L ⊤) w :
      τ l w = ClassicalOrthogonal.FourPlusMatrix.matrixAction (e l) w := by
    change ClassicalOrthogonal.FourPlusMatrix.coordinates
      (c ((F.terminalRepresentation.comp (componentOrbit L ⊤).subtype) l (d.symm w))) = _
    rw [hc]
    have he : ClassicalOrthogonal.FourPlusMatrix.toOrthogonal (e l) = (a l).val :=
      congrArg Subtype.val
        ((ClassicalOrthogonal.FourPlusMatrix.elementaryEquiv (F := k)).apply_symm_apply (a l))
    change ClassicalOrthogonal.FourPlusMatrix.coordinates ((a l).val.val (c (d.symm w))) = _
    rw [←he,ClassicalOrthogonal.FourPlusMatrix.toOrthogonal_coordinates]
    exact congrArg (ClassicalOrthogonal.FourPlusMatrix.matrixAction (e l)) (d.apply_symm_apply w)
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  obtain ⟨φ,hφ⟩ := ClassicalOrthogonal.FourPlusMatrix.normal_ambient_semilinear
    (componentOrbit L ⊤) e τ hτ
  let : Module k (Additive F.Uhat) := Representation.SymplecticFixedLine.coordinateModule d
  have hsmul (a : k) (w : Additive F.Uhat) : d (a • w) = a • d w := d.apply_symm_apply _
  let : SMulCommClass k (ZMod 2) (Additive F.Uhat) := ⟨fun a b w => by
    apply d.injective
    simp only [hsmul,d.map_smul,smul_comm a b]⟩
  let : IsScalarTower (ZMod 2) k (Additive F.Uhat) :=
    IsScalarTower.of_algebraMap_smul (fun a w => by
      apply d.injective
      rw [hsmul,d.map_smul]
      exact IsScalarTower.algebraMap_smul k a (d w))
  have hsemi (x : F.terminalDot (F.X g)) (a : k) w :
      F.terminalRepresentation x (a • w) = φ x a • F.terminalRepresentation x w := by
    apply d.injective
    rw [hsmul]
    have he := hφ (x : F.TerminalHdot) a (d w)
    change d (F.terminalRepresentation x (d.symm (a • d w))) =
      φ x a • d (F.terminalRepresentation x (d.symm (d w))) at he
    rw [d.symm_apply_apply] at he
    have hh : d.symm (a • d w) = a • w := d.injective (by rw [d.apply_symm_apply,hsmul])
    rwa [hh] at he
  have hb := s.coefficient_card_le_four_of_actor_semilinear (k := k)
    (by omega) (φ.comp (F.terminalDot (F.X g)).subtype) hsemi
  change Nat.card (GaloisField 2 n) ≤ 4 at hb
  rw [GaloisField.card 2 n (by omega)] at hb
  have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  have hnEq : n = 2 := by omega
  omega

/-- At degree eight the original component is A₅ and its actual orbit action
is the binary determinant tensor. The next consumer discharges the degree premise from the source geometry. -/
theorem whole_pair_eight (hi : I = ⊤) (hne : componentOrbit L ⊤ ≠ L)
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 8) :
    Nonempty (L ≃* alternatingGroup (Fin 5)) ∧
      Quasiequivalent (F.terminalRepresentation.comp (componentOrbit L ⊤).subtype)
        ClassicalOrthogonal.FourPlusMatrix.Binary.action := by
  obtain ⟨n,_,hdeg,⟨e⟩,a,c,hc⟩ := s.whole_pair_recognition hi hne
  have hn : n = 2 := by omega
  subst n
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    norm_num [GaloisField.card 2 2 (by decide)]
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcard
  refine ⟨⟨e.trans ((Theory.PSL2.sl2QuotientEquiv _).trans eA)⟩,?_,?_,?_⟩
  · exact a.trans ClassicalOrthogonal.FourPlusMatrix.Binary.galoisGroupEquiv
  · exact c.trans ClassicalOrthogonal.FourPlusMatrix.Binary.galoisCoordinates
  · intro l w
    change ClassicalOrthogonal.FourPlusMatrix.Binary.galoisCoordinates
      (c ((F.terminalRepresentation.comp (componentOrbit L ⊤).subtype) l w)) = _
    rw [hc]
    exact ClassicalOrthogonal.FourPlusMatrix.Binary.galoisCoordinates_intertwines (a l) (c w)

/-- Construct the ActionModel on the literal dotted T-conjugate span. The
model's form transport preserves the original B, its nondegeneracy and invariance. -/
theorem actionModel_of_whole_pair_eight (hi : I = ⊤) (hne : componentOrbit L ⊤ ≠ L)
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 8)
    {K : Subgroup G} (hK : ComponentLift F g K) (he : F.terminalDot K = L) :
    Nonempty (ExchangedA5.ActionModel F K) := by
  obtain ⟨_,a,c,hc⟩ := s.whole_pair_eight hi hne hd
  have hspan : F.terminalDot (conjugateSpanBy K (T : Subgroup G)) = componentOrbit L ⊤ := by
    rw [hK.terminalDot_span_eq_componentOrbit,he]
  refine ⟨⟨(MulEquiv.subgroupCongr hspan).trans a,c,?_⟩⟩
  intro k w
  exact hc ((MulEquiv.subgroupCongr hspan) k) w

/-- The degree-eight two-component branch supplies the literal local lift,
the catalogue row and genuine tensor ActionModel together. -/
theorem local_lift_and_actionModel_of_whole_pair_eight
    (hi : I = ⊤) (hne : componentOrbit L ⊤ ≠ L)
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 8) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K ∧
      Nonempty (ExchangedA5.ActionModel F K) := by
  have hc : ComponentImageCases L := Or.inr (Or.inl (Or.inl (s.whole_pair_eight hi hne hd).1))
  obtain ⟨K,hKH,hlocal,hcomp,he,_,hnormal⟩ :=
    Recognition.terminal_component_lift s.simple F (by decide) L s.component
  change F.terminalDot K = L at he
  have hK : ComponentLift F g K :=
    ⟨hKH,hlocal,hcomp,he.symm ▸ s.component,he.symm ▸ s.moved,hnormal⟩
  refine ⟨K,hK,?_,s.actionModel_of_whole_pair_eight hi hne hd hK he⟩
  exact source_component_cases_of_small_actor s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.hypothesis s.small_actor hK (he.symm ▸ hc)

/-- Every whole marked component pair has the small A₅ image. -/
theorem imageCases_of_whole_pair (hi : I = ⊤) (hne : componentOrbit L ⊤ ≠ L) :
    s.ImageCases := by
  obtain ⟨e⟩ := (s.whole_pair_eight hi hne (s.degree_eight_of_whole_pair hi hne)).1
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
  let eL := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
  exact Or.inr (Or.inl (Or.inl ⟨eL.symm.trans e⟩))

/-- The original whole pair supplies a literal local lift and the genuine
tensor model, with its degree and field premises fully discharged. -/
theorem local_lift_and_actionModel_of_whole_pair
    (hi : I = ⊤) (hne : componentOrbit L ⊤ ≠ L) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K ∧
      Nonempty (ExchangedA5.ActionModel F K) :=
  s.local_lift_and_actionModel_of_whole_pair_eight hi hne (s.degree_eight_of_whole_pair hi hne)

/-- All marked branches except the whole single-component branch are now
proved. The original FixedPointAlternative is retained for that remaining proof. -/
theorem imageCases_of_whole_single_recognition
    (hsingle : ActorFaithful (F := F) (g := g) (I := I) → I = ⊤ →
      componentOrbit L ⊤ = L →
      FixedPointAlternative (F := F) (g := g) (v := v) → s.ImageCases) : s.ImageCases := by
  apply s.imageCases_of_whole_faithful_recognition
  intro hf hi hfp
  by_cases he : componentOrbit L ⊤ = L
  · exact hsingle hf hi he hfp
  · exact s.imageCases_of_whole_pair hi he

/-- The original local lift now requires only whole single-component recognition. -/
theorem local_lift_of_whole_single_recognition
    (hsingle : ActorFaithful (F := F) (g := g) (I := I) → I = ⊤ →
      componentOrbit L ⊤ = L →
      FixedPointAlternative (F := F) (g := g) (v := v) → s.ImageCases) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_whole_single_recognition hsingle)

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
