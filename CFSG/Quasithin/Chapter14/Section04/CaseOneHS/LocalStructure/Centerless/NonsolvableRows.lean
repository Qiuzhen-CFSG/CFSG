module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.ComponentLift
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.Thompson
public import CFSG.Quasithin.ChapterG.Section11.Catalogue
public import Theory.Representation.BinaryFourQuintic
public import Theory.Representation.G2NaturalBinary
public import Theory.Representation.RepEquiv
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# The nonsolvable six-letter and natural G2 seed rows

The literal A6/S6 quotients have solvable residual A6. An order-five
actor makes its faithful binary four-space irreducible. The natural G2(2)
row has the actual simple derived octonion group as residual, of order
6048, and its checked natural module is irreducible. Transport uses the
restriction of the original quotient isomorphism in each case.

These facts construct every clause of NonsolvableSeedRow in these three
source alternatives. The faithful-component argument then proves the seed
exclusion. Its A6 centerlessness and LocalStructure applications and the
G2 Thompson-containment application are included.

The S5 marking and S6 centerlessness argument are supplied by the later
NonsolvableFive and SymmetricSix extensions. The earlier exhaustive alternatives
and G2 and Goldschmidt centerlessness contradictions remain with this owner.
No later theorem assuming centerlessness is used. The authorized earlier
faithful classification remains explicit; final discharge stays with
qt-d-hs-local-structure.
Source: Aschbacher--Smith 14.3.23--25 and 14.3.29--31, pp.1000--1003.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem residual_equiv_six {D : Type*} [Group D] [Finite D]
    (model : Nonempty (D ≃* alternatingGroup (Fin 6)) ∨ Nonempty (D ≃* Equiv.Perm (Fin 6))) :
    Nonempty (solvableResidual D ≃* alternatingGroup (Fin 6)) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  rcases model with model | model
  · obtain ⟨e⟩ := model
    have he : (solvableResidual D).map e.toMonoidHom = ⊤ := by
      rw [map_solvableResidual_eq _ e.surjective,solvableResidual_eq_top]
    exact ⟨(e.subgroupMap _).trans ((MulEquiv.subgroupCongr he).trans Subgroup.topEquiv)⟩
  · obtain ⟨e⟩ := model
    have hr : solvableResidual (Equiv.Perm (Fin 6)) = alternatingGroup (Fin 6) := by
      apply le_antisymm
      · exact (solvableResidual_le_derivedSeries 1).trans_eq
          (alternatingGroup.commutator_perm_eq (by simp))
      · exact le_solvableResidual_of_isPerfect _
    have he : (solvableResidual D).map e.toMonoidHom = alternatingGroup (Fin 6) := by
      rw [map_solvableResidual_eq _ e.surjective,hr]
    exact ⟨(e.subgroupMap _).trans (MulEquiv.subgroupCongr he)⟩

/-- Construct the nonsolvable seed row from the literal A6/S6 quotient on a four-space. -/
theorem source_nonsolvable_six_seed_row
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (model : Nonempty (Hdot F F.uhatAction ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 6))) (g : G) :
    NonsolvableSeedRow F g := by
  obtain ⟨e⟩ := residual_equiv_six model
  have hc : Nat.card (solvableResidual (Hdot F F.uhatAction)) = 360 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 6)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  refine ⟨IsQuasisimple.of_mulEquiv e.symm,?_,.inr (.inl hc),?_⟩
  · let ρ := elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction)
    have hf : Function.Injective ρ := by
      intro a b hab
      apply faithfulAction_injective F F.uhatAction
      ext w
      exact congrArg Additive.toMul (LinearMap.congr_fun hab (Additive.ofMul w))
    exact binary_four_irreducible_of_five_dvd
      (ρ.comp (solvableResidual (Hdot F F.uhatAction)).subtype)
      (hf.comp (solvableResidual (Hdot F F.uhatAction)).subtype_injective)
      hd (by rw [hc]; decide)
  · intro hh
    omega

/-- The seed exclusion for both original degree-four six-letter rows. -/
theorem source_seed_exclusion_of_six_model (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 6))) : centralLTSeed F L = ⊥ := by
  let := chosen.elementary
  obtain ⟨htwo,hphi,_⟩ := source_closure d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    rw [hc,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (a := 2) (by decide)
      (show 2^4 = 2^finrank (ZMod 2) (Additive F.Uhat) from hh)).symm
  obtain ⟨g,hgP,hgH⟩ := source_conjugator d earlier hq chosen structural F
  exact source_seed_exclusion_of_dotted_row d earlier hq chosen structural alternatives
    classification F hne g hgP hgH (source_nonsolvable_six_seed_row F hd model g)

/-- The A6 centerlessness branch with the earlier marked row constructed. -/
theorem source_centerless_of_alternatingSix_model (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* alternatingGroup (Fin 6))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ :=
  source_centerless_of_alternatingSix d earlier hq chosen structural alternatives F hne
    (source_seed_exclusion_of_six_model d earlier hq chosen structural alternatives
      classification F hne hc (.inl model)) model


private theorem binaryG2_residual :
    solvableResidual (Atlas.G2.Model (ZMod 2)) = commutator (Atlas.G2.Model (ZMod 2)) := by
  let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) := by
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.H_isPerfect
  exact le_antisymm (solvableResidual_le_derivedSeries 1) (le_solvableResidual_of_isPerfect _)

/-- The literal six-dimensional natural G2(2) row supplies its simple residual and action. -/
theorem source_nonsolvable_g2_seed_row
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (model : ChapterG.Section11.CaseSix
      (elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction))) (g : G) :
    NonsolvableSeedRow F g := by
  obtain ⟨_,e,c,he⟩ := model
  let R := solvableResidual (Hdot F F.uhatAction)
  let D := commutator (Atlas.G2.Model (ZMod 2))
  have hm : R.map e.toMonoidHom = D := by
    rw [map_solvableResidual_eq _ e.surjective,binaryG2_residual]
  let r : R ≃* D := (e.subgroupMap R).trans (MulEquiv.subgroupCongr hm)
  have hc : Nat.card R = 6048 :=
    (Nat.card_congr r.toEquiv).trans Atlas.G2.LieAutomorphismExtensions.card_binaryDerived
  let : Group.IsPerfect D :=
    Group.IsPerfect.ofSurjective (f := r.toMonoidHom) r.surjective
  let : IsSimpleGroup D := Atlas.G2.isSimple_commutator_binary
  have hz : center D = ⊥ := by
    rcases (inferInstance : (center D).Normal).eq_bot_or_eq_top with hh | hh
    · exact hh
    · let := center_eq_top_iff.mp hh
      exact (Group.IsPerfect.not_isSolvable D inferInstance).elim
  let : IsQuasisimple D :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  refine ⟨IsQuasisimple.of_mulEquiv r.symm,?_,.inr (.inr hc),?_⟩
  · let ρ := (elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction)).comp R.subtype
    let σ := (Atlas.G2.Natural.derivedAction (ZMod 2)).comp r.toMonoidHom
    have hi : IsIrreducible σ :=
      (irreducible_comp_surjective_iff r.toMonoidHom r.surjective _).mpr
        Atlas.G2.Natural.Binary.natural_irreducible
    let E : RepEquiv ρ σ := {
      toLinearEquiv := c
      isIntertwining' a := by ext w; exact he a w }
    exact E.irreducible_of_euqiv hi
  · intro hh
    change Nat.card R = 60 at hh
    omega

/-- The G2 natural branch of 14.3.25, with its nonsolvable marked row constructed. -/
theorem source_seed_exclusion_of_g2_natural (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (model : ChapterG.Section11.CaseSix
      (elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction))) :
    centralLTSeed F L = ⊥ := by
  obtain ⟨g,hgP,hgH⟩ := source_conjugator d earlier hq chosen structural F
  exact source_seed_exclusion_of_dotted_row d earlier hq chosen structural alternatives
    classification F hne g hgP hgH (source_nonsolvable_g2_seed_row F model g)

/-- The original Thompson containment in the G2 branch no longer assumes a seed row. -/
theorem source_g2_natural_thompson_le_plane_core (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (model : ChapterG.Section11.CaseSix
      (elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction)))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ (F.I₂ L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  exact source_contrary_thompson_le_plane_core d earlier hq chosen structural alternatives F hne
    (source_seed_exclusion_of_g2_natural d earlier hq chosen structural alternatives
      classification F hne model) hI

/-- Literal LocalStructure application of the completed A6 seed and centerlessness branch. -/
theorem localStructure_of_alternatingSix_model_action (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* alternatingGroup (Fin 6)))
    (action : ActionStructure F) : LocalStructure L F :=
  localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne
    (source_centerless_of_alternatingSix_model d earlier hq chosen structural alternatives
      classification F hne hc model) action

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
