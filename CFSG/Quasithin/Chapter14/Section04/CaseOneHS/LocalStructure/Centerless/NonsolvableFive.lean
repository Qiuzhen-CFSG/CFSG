module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.NonsolvableRows
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.EarlierNontrivial
public import Theory.SpecificGroups.SymmetricFive.MarkedPlaneKernel

/-!
# The original symmetric-five marked row and centerlessness branch

The original Sylow image stabilizes the seed plane. Its elementary actor
has order at most four and acts nontrivially on that plane, while the
conjugate center fixes it pointwise. The nontrivial plane kernel therefore
has order two. Sylow normalization puts this kernel in the alternating
residual, establishing the literal marking required by 14.3.23(2)(ii).
An order-five actor gives irreducibility of that residual on the binary
four-space. The proved faithful-component argument now discharges 14.3.25
and the existing marked-plane contradiction gives centerlessness.

The final theorem applies the S5/A6 branches to LocalStructure. Its action
premise is independent of the centerlessness proofs. The earlier exhaustive
alternatives and remaining G2 and Goldschmidt arguments are still owned by
qt-d-hs-centerless-source; authorized earlier inputs are retained for final
discharge by qt-d-hs-local-structure. Import this extension directly, because
EarlierNontrivial lies above the lower Centerless umbrella.
Source: Aschbacher--Smith 14.3.23(2)(ii), 14.3.25 and 14.3.31,
printed pp.1000--1003, refs/quasithin.pdf.
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

/-- The original four-space Sylow geometry supplies the A5 marking of the conjugate center. -/
theorem source_symmetricFive_marked_center (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 5)))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    Nat.card (dotImage F F.uhatAction (conjugate F.ZU g)) = 2 ∧
      dotImage F F.uhatAction (conjugate F.ZU g) ≤ solvableResidual (Hdot F F.uhatAction) := by
  let := chosen.elementary
  obtain ⟨_,hX,B,v,hyp,hline,hfix⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let : IsElementaryAbelian 2 (F.terminalDot (F.X g)) := hX
  obtain ⟨_,hE,_,_⟩ := source_four_marked_geometry d earlier hq chosen structural alternatives
    F hne hd g hgP hgH
  let S := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXS,hXN⟩ := source_earlier_actor_normal_in_sylow d earlier hq chosen structural alternatives
    F hne g hgP hgH
  have hSN : (S : Subgroup F.TerminalHdot) ≤
      normalizer (F.terminalDot (F.X g) : Set F.TerminalHdot) :=
    (normal_subgroupOf_iff_le_normalizer hXS).mp hXN
  have hSU : ∀ s ∈ S, ∀ w ∈ hatSpace F V, F.terminalRepresentation s w ∈ hatSpace F V := by
    rintro s ⟨a,ha,rfl⟩ w ⟨u,hu,heu⟩
    have hn : (a:G) ∈ normalizer (V : Set G) := by
      have hh : (a : G) ∈ normalizer (F.Vi 3 : Set G) := F.invariant 3 ha
      rwa [F.last] at hh
    refine ⟨F.uAction a u,(mem_normalizer_iff.mp hn (u:G)).mp hu,?_⟩
    change QuotientGroup.mk' (center F.U) (F.uAction a u) = F.uhatAction a w.toMul
    rw [←F.uhatAction_apply_mk,heu]
  have hnot : ¬ hatSpace F V ≤ BinaryOffender.fixedSpace F.terminalRepresentation
      (F.terminalDot (F.X g)) := by
    intro hh
    have he := congrArg (fun W : Submodule (ZMod 2) (Additive F.Uhat) => finrank (ZMod 2) W) hyp.fixedSpace_in_W
    rw [hE,inf_eq_left.mpr hh,seed_hat_dimension F
      (source_closure d earlier hq chosen structural alternatives F hne).2.2,
      finrank_span_singleton hyp.point_ne_zero] at he
    omega
  obtain ⟨e⟩ := model
  exact Theory.SpecificGroups.SymmetricFive.marked_plane_kernel (D := F.TerminalHdot)
    e F.terminalRepresentation
    (hatSpace F V) S (F.terminalDot (F.X g)) (F.terminalDot (conjugate F.ZU g))
    hXS hSN hSU (map_mono (comap_mono (F.conjugate_ZU_le_X g)))
    (source_earlier_conjugate_center_ne_bot d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH)
    (source_conjugate_center_fixes_seed chosen F g hgP) hnot

/-- Every clause of the original S5 seed row follows from its literal model and marked flag. -/
theorem source_nonsolvable_five_seed_row (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 5)))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : NonsolvableSeedRow F g := by
  obtain ⟨e⟩ := model
  have hm : (solvableResidual (Hdot F F.uhatAction)).map e.toMonoidHom =
      solvableResidual (Equiv.Perm (Fin 5)) := map_solvableResidual_eq _ e.surjective
  let r := (e.subgroupMap (solvableResidual (Hdot F F.uhatAction))).trans (MulEquiv.subgroupCongr hm)
  let := Theory.SpecificGroups.SymmetricFive.WreathComponents.symmetric_residual_quasisimple
  have hc : Nat.card (solvableResidual (Hdot F F.uhatAction)) = 60 := by
    rw [Nat.card_congr r.toEquiv,Theory.SpecificGroups.SymmetricFive.WreathComponents.symmetric_residual,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  refine ⟨IsQuasisimple.of_mulEquiv r.symm,?_,.inl hc,?_⟩
  · exact binary_four_irreducible_of_five_dvd
      (F.terminalRepresentation.comp (solvableResidual F.TerminalHdot).subtype)
      (F.terminalRepresentation_injective.comp (solvableResidual F.TerminalHdot).subtype_injective)
      hd (by
        change 5 ∣ Nat.card (solvableResidual (Hdot F F.uhatAction))
        rw [hc]
        decide)
  · intro _
    exact (source_symmetricFive_marked_center d earlier hq chosen structural alternatives
      F hne hZ hd ⟨e⟩ g hgP hgH).symm

/-- The S5 branch of 14.3.25 with the marked row, component and seed premises discharged. -/
theorem source_seed_exclusion_of_five_model (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 5))) : centralLTSeed F L = ⊥ := by
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
    classification F hne g hgP hgH
    (source_nonsolvable_five_seed_row d earlier hq chosen structural alternatives
      F hne hZ hd model g hgP hgH)

/-- The original S5 centerlessness branch with no marked-row or seed-exclusion callback. -/
theorem source_centerless_of_symmetricFive_model (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 5))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ :=
  source_centerless_of_symmetricFive d earlier hq chosen structural alternatives F hne
    (source_seed_exclusion_of_five_model d earlier hq chosen structural alternatives
      classification F hne hZ hc model) model

/-- The literal local-structure application in both small nonsolvable rows. -/
theorem localStructure_of_small_nonsolvable_model_action (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 5)) ∨
      Nonempty (Hdot F F.uhatAction ≃* alternatingGroup (Fin 6)))
    (action : ActionStructure F) : LocalStructure L F := by
  apply localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne _ action
  rcases model with model | model
  · exact source_centerless_of_symmetricFive_model d earlier hq chosen structural alternatives
      classification F hne hZ hc model
  · exact source_centerless_of_alternatingSix_model d earlier hq chosen structural alternatives
      classification F hne hc model

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
