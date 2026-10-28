module

public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource.ComponentStructure
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.SourceCatalogue
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The component list attached to the same B.4.2 action

Extract the B.5.5(1iv) component list from every row of the corrected B.4.2
catalogue through an actual isomorphism from the original L. Perfection of L
identifies the large symplectic and G₂ actors with their commutator groups.
The small endpoints use the established A₅/SL₂(4), A₆/Sp₄(2)' and A₈/SL₄(2)
equivalences. The triple-A₆ row preserves both the cubic center and the literal
central quotient. The ChiefSections assembly applies this to the marked
component of its original chief section.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.5(1iv), printed pp.104–105; B.4.2, printed p.86.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.PreparationSource.ChiefSections
open SourceInduction ComponentReduction ComponentReduction.PreliminaryActions Preparation
open QuasisimpleSource
universe u v w

private noncomputable def alternatingFiveEquiv :
    alternatingGroup (Fin 5) ≃* Matrix.SpecialLinearGroup (Fin 2) BinaryField.four.Carrier :=
  (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := BinaryField.four.Carrier) (by
      change Nat.card (GaloisField 2 2) = 4
      rw [GaloisField.card 2 2 (by decide)]
      decide)).some.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans
        QuotientGroup.quotientBot)

private noncomputable def alternatingSixEquiv :
    alternatingGroup (Fin 6) ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  exact ((e.subgroupMap _).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    exact alternatingGroup.commutator_perm_eq (by norm_num)))).symm

private noncomputable def alternatingEightEquiv :
    alternatingGroup (Fin 8) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans Atlas.Order20160A8.sl4TwoEquivPSL.symm

private noncomputable def derivedEquiv {X : Type*} [Group X] [Group.IsPerfect X] :
    X ≃* commutator X :=
  topEquiv.symm.trans (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm)

/-- Extract B.5.5's complete component list through the marked original L.
Perfection of L identifies the large symplectic and G₂ actors with their
derived groups; the small endpoints use the actual exceptional isomorphisms. -/
theorem models_of_actions
    {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {E : Type w} [Group E] {L : Subgroup E} [IsQuasisimple L]
    {σ : Representation (ZMod 2) D V} {M H : Subgroup D}
    (eL : L ≃* M) (h : ProjectiveLine.IrreducibleActionCase σ M H) : ComponentModels L := by
  cases h with
  | linearTwo F _ e _ _ => exact Or.inl ⟨F, ⟨eL.trans e.groupEquiv⟩⟩
  | linearThree F _ e _ => exact Or.inr (Or.inl ⟨F, ⟨eL.trans e.groupEquiv⟩⟩)
  | symplectic F _ _ e _ =>
    let q := eL.trans e.groupEquiv
    let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) F.Carrier) :=
      Group.IsPerfect.ofSurjective (f := q.toMonoidHom) q.surjective
    exact Or.inr (Or.inr (Or.inl ⟨F, ⟨q.trans derivedEquiv⟩⟩))
  | symplecticTwo e _ =>
    exact Or.inr (Or.inr (Or.inl ⟨BinaryField.two, ⟨eL.trans e.subgroupEquiv⟩⟩))
  | g2 F _ _ e _ _ =>
    let q := eL.trans e.groupEquiv
    let : Group.IsPerfect (Atlas.G2.Model F.Carrier) :=
      Group.IsPerfect.ofSurjective (f := q.toMonoidHom) q.surjective
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨F, ⟨q.trans derivedEquiv⟩⟩)))
  | g2Two e _ _ =>
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨BinaryField.two, ⟨eL.trans e.subgroupEquiv⟩⟩)))
  | symmetric n hn e _ _ =>
    rcases hn with rfl | rfl
    · exact Or.inl ⟨BinaryField.four, ⟨eL.trans (e.subgroupEquiv.trans alternatingFiveEquiv)⟩⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eL.trans e.subgroupEquiv⟩))))
  | alternatingSix _ e _ _ =>
    exact Or.inr (Or.inr (Or.inl ⟨BinaryField.two,
      ⟨eL.trans (e.groupEquiv.trans alternatingSixEquiv)⟩⟩))
  | alternatingSeven _ _ e _ _ _ =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eL.trans e⟩))))
  | tripleSix _ a _ =>
    have hc : (center L).map eL.toMonoidHom = center M := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (centerCongr eL ⟨y, hy⟩).property
      · intro hx
        exact ⟨eL.symm x, (centerCongr eL.symm ⟨x, hx⟩).property, eL.apply_symm_apply x⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨(centerCongr eL).trans a.centerEquiv⟩,
       ⟨(QuotientGroup.congr _ _ eL hc).trans a.quotientEquiv⟩⟩)))))
  | binaryLinear d hd _ e _ =>
    rcases hd with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eL.trans e.groupEquiv⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨eL.trans e.groupEquiv⟩))))))
  | orthogonalSix _ _ e _ _ =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨eL.trans (e.groupEquiv.trans alternatingEightEquiv)⟩))))))
  | symmetricEight _ e _ =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨eL.trans (e.subgroupEquiv.trans alternatingEightEquiv)⟩))))))
  | exteriorFive _ _ e _ _ _ =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨eL.trans e⟩))))))

end CFSG.Quasithin.ChapterB.PreparationSource.ChiefSections
