module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraphAmalgam
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension
public import Theory.GroupTheory.SolvableResidual

/-!
# The marked graph-fixed diagram in a projective unitary-four comparison

The faithful SU₄ projectivization transports the native graph centralizer
and its two parabolics to the literal degree-two projective extension.
Every compatible comparison, in either orientation, therefore supplies an
involution outside both solvable residuals and an isomorphism of its full
fixed local diagram with the symplectic diagram times C₂. The middle map
sends this very involution to the central C₂ generator, retaining the kernel
for the subsequent quotient by the graph involution.

Source: Aschbacher–Smith F.4.37(1–3), printed p.293 of `refs/quasithin.pdf`,
for the native degree-two comparison. Extension to the original full
normalizers and ambient centralizer Sylow placement remain further steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.UnitarySource.FourGraph
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
variable (m : ℕ) (hm : 1 ≤ m)

abbrev fixedDiagram := productDiagram (MatrixField m) (fieldConj m)

private theorem graph_not_residual (P : Subgroup (Extension.MatrixExtension m hm))
    (hf : UnitaryFourOuter.sigma (MatrixField m) (fieldConj m)
      (fieldConj_involutive m hm) ∈ P) :
    (⟨UnitaryFourOuter.sigma (MatrixField m) (fieldConj m)
      (fieldConj_involutive m hm),hf⟩ : P) ∉ solvableResidual P := by
  intro hx
  let f : P →* UnitaryFourOuter.C2 := SemidirectProduct.rightHom.comp P.subtype
  have he := map_solvableResidual_le f (mem_map_of_mem f hx)
  rw [solvableResidual_eq_bot] at he
  change UnitaryFourOuter.generator = 1 at he
  exact (by decide : UnitaryFourOuter.generator ≠ 1) he

private theorem transported_graph
    {L B R : Type*} [Group L] [Group B] [Group R]
    (α : RankTwoAmalgam L B R)
    (e : RankTwoAmalgam.Iso α (Extension.matrixAmalgam m hm)) :
    ∃ b : B, orderOf b = 2 ∧ α.left b ∉ solvableResidual L ∧
      α.right b ∉ solvableResidual R ∧
      ∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) (fixedDiagram m),
        e.middle (centralPoint b) = (1,UnitaryFourOuter.generator) := by
  let a := graphElement (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
  let b := e.middle.symm a
  have ha : a^2=1 := Subtype.ext
    (UnitaryFourOuter.sigma_sq (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))
  have ha1 : a ≠ 1 := fun he =>
    UnitaryFourOuter.sigma_ne_one (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
      (congrArg Subtype.val he)
  have hb : e.middle b = a := e.middle.apply_symm_apply a
  refine ⟨b, orderOf_eq_prime (e.middle.injective (by rw [map_pow,hb,ha,map_one]))
    (fun he => ha1 (hb.symm.trans (he ▸ e.middle.map_one))), ?_, ?_, ?_⟩
  · intro hx
    have hx' := map_solvableResidual_le e.left.toMonoidHom (mem_map_of_mem _ hx)
    change e.left (α.left b) ∈ _ at hx'
    rw [e.left_commutes,hb] at hx'
    exact graph_not_residual m hm _ (UnitaryFourOuter.sigma_mem_overlap _ _ _).1 hx'
  · intro hx
    have hx' := map_solvableResidual_le e.right.toMonoidHom (mem_map_of_mem _ hx)
    change e.right (α.right b) ∈ _ at hx'
    rw [e.right_commutes,hb] at hx'
    exact graph_not_residual m hm _ (UnitaryFourOuter.sigma_mem_overlap _ _ _).2 hx'
  · let j := graphDiagramIso (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
    refine ⟨(centralizerTransport e a).trans j.symm,?_⟩
    change j.middle.symm ((centralizerTransport e a).middle (centralPoint b)) = _
    rw [centralizerTransport_self]
    apply j.middle.injective
    rw [j.middle.apply_symm_apply]
    exact (graphDiagramIso_graph (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)).symm

private theorem projective_graph
    {L B R : Type*} [Group L] [Group B] [Group R]
    (α : RankTwoAmalgam L B R)
    (e : RankTwoAmalgam.Iso α (Extension.amalgam m hm)) :
    ∃ b : B, orderOf b = 2 ∧ α.left b ∉ solvableResidual L ∧
      α.right b ∉ solvableResidual R ∧
      ∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) (fixedDiagram m),
        e.middle (centralPoint b) = (1,UnitaryFourOuter.generator) :=
  transported_graph m hm α (e.trans (Extension.projectIso m hm).symm)

private def reverseSource
    {L B R X Y Z : Type*} [Group L] [Group B] [Group R] [Group X] [Group Y] [Group Z]
    {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam X Y Z}
    (e : RankTwoAmalgam.Iso α β.reverse) : RankTwoAmalgam.Iso α.reverse β := e.reverse

private theorem reverseFixed
    {L B R X Y Z : Type*} [Group L] [Group B] [Group R] [Group X] [Group Y] [Group Z]
    {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam X Y Z} (b : B) (y : Y)
    (h : ∃ e : RankTwoAmalgam.Iso (centralizerDiagram α.reverse b) β,
      e.middle (centralPoint b) = y) :
    ∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) β.reverse,
      e.middle (centralPoint b) = y := by
  obtain ⟨e,he⟩ := h
  exact ⟨e.reverse,he⟩

/-- A whole-overlap degree-two comparison constructs an actual outer involution
and its complete fixed local diagram, retaining either endpoint orientation. -/
theorem comparison_graph
    {L B R : Type*} [Group L] [Group B] [Group R]
    (α : RankTwoAmalgam L B R)
    (hc : Nonempty (RankTwoAmalgam.Iso α (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso α (Extension.amalgam m hm).reverse)) :
    ∃ b : B, orderOf b = 2 ∧ α.left b ∉ solvableResidual L ∧
      α.right b ∉ solvableResidual R ∧
      ((∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) (fixedDiagram m),
          e.middle (centralPoint b) = (1,UnitaryFourOuter.generator)) ∨
       (∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) (fixedDiagram m).reverse,
          e.middle (centralPoint b) = (1,UnitaryFourOuter.generator))) := by
  apply hc.elim
  · intro he
    exact he.elim fun e => (projective_graph m hm α e).imp fun b hb =>
      ⟨hb.1,hb.2.1,hb.2.2.1,Or.inl hb.2.2.2⟩
  · intro he
    exact he.elim fun e =>
      (projective_graph m hm α.reverse (reverseSource (β := Extension.amalgam m hm) e)).imp
        fun b hb => ⟨hb.1,hb.2.2.1,hb.2.1,
          Or.inr (reverseFixed (α := α) (β := fixedDiagram m) b _ hb.2.2.2)⟩


private theorem conjugate_in_sylow {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) (x : X) (hx : orderOf x = 2) :
    ∃ g : X, g*x*g⁻¹ ∈ (P : Subgroup X) := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,hx]
    decide)
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq X S P
  refine ⟨g,?_⟩
  rw [←hg]
  exact ⟨x,hS (mem_zpowers x),rfl⟩

private theorem conj_not_residual {X Y : Type*} [Group X] [Group Y]
    (φ : X →* Y) (x g : X) (hx : φ x ∉ solvableResidual Y) :
    φ (g*x*g⁻¹) ∉ solvableResidual Y := by
  intro h
  have hh := (inferInstance : (solvableResidual Y).Normal).conj_mem _ h (φ g)⁻¹
  have he : (φ g)⁻¹ * φ (g*x*g⁻¹) * ((φ g)⁻¹)⁻¹ = φ x := by
    rw [map_mul,map_mul,map_inv]
    group
  exact hx (he ▸ hh)

private theorem conjugateFixed
    {L B R X Y Z : Type*} [Group L] [Group B] [Group R] [Group X] [Group Y] [Group Z]
    {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam X Y Z} (b c : B) (y : Y)
    (h : ∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) β,
      e.middle (centralPoint b) = y) :
    ∃ e : RankTwoAmalgam.Iso (centralizerDiagram α (c*b*c⁻¹)) β,
      e.middle (centralPoint (c*b*c⁻¹)) = y := by
  obtain ⟨e,he⟩ := h
  refine ⟨(centralizerConjugate α b c).trans e,?_⟩
  change e.middle ((centralizerConjugate α b c).middle (centralPoint (c*b*c⁻¹))) = _
  rw [centralizerConjugate_self]
  exact he

/-- The marked graph involution can be placed in any specified Sylow of the
original whole overlap, preserving both fixed endpoints and the central kernel. -/
theorem comparison_graph_sylow
    {L B R : Type*} [Group L] [Group B] [Group R] [Finite B]
    (α : RankTwoAmalgam L B R) (U : Sylow 2 B)
    (hc : Nonempty (RankTwoAmalgam.Iso α (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso α (Extension.amalgam m hm).reverse)) :
    ∃ b : B, b ∈ (U : Subgroup B) ∧ orderOf b = 2 ∧
      α.left b ∉ solvableResidual L ∧ α.right b ∉ solvableResidual R ∧
      ((∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) (fixedDiagram m),
          e.middle (centralPoint b) = (1,UnitaryFourOuter.generator)) ∨
       (∃ e : RankTwoAmalgam.Iso (centralizerDiagram α b) (fixedDiagram m).reverse,
          e.middle (centralPoint b) = (1,UnitaryFourOuter.generator))) := by
  refine (comparison_graph m hm α hc).elim fun b hb => ?_
  obtain ⟨g,hg⟩ := conjugate_in_sylow U b hb.1
  refine ⟨g*b*g⁻¹,hg,((MulAut.conj g).orderOf_eq b).trans hb.1,
    conj_not_residual α.left b g hb.2.1,
    conj_not_residual α.right b g hb.2.2.1,?_⟩
  exact hb.2.2.2.elim
    (fun he => Or.inl (conjugateFixed (α := α) (β := fixedDiagram m) b g _ he))
    (fun he => Or.inr (conjugateFixed (α := α) (β := (fixedDiagram m).reverse) b g _ he))

end CFSG.Quasithin.ChapterF.UnitarySource.FourGraph
