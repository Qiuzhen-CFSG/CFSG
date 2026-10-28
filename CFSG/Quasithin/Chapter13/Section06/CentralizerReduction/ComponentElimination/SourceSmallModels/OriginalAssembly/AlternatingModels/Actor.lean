module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingModels.Classifier
public import Theory.SpecificGroups.AlternatingSevenNormalControl
public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer

/-!
# Full A₇ action models before short-block recognition

The faithful plus actor embeds in Aut(A₇), of order 5040. In the natural
B.5 row its marked S₇ subgroup therefore fills the actor. In the exceptional
four-dimensional row, the faithful normal A₇ image is self-normalizing in
GL₄(2), so it likewise fills the actor. Thus best offenders generate the
whole original group, and complete B.5.1 applies directly to its action.

The A₇ order excludes every nonsplit and supplement row. The resulting
full moved module has a pointwise-fixed complement and no central kernel.
Its natural chart retains the literal A₇ image, all subgroup fixed
codimensions, and an equivariant inclusion into the original module.

Source: Aschbacher–Smith B.5.1, pp.99–103, and 13.6.22, p.932.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingModels
universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (C : Subgroup D) [C.Normal]

omit [Finite D] [Module.Finite (ZMod 2) V] in
theorem card_le_symmetricSeven (eC : C ≃* alternatingGroup (Fin 7))
    (hC : centralizer (C : Set D) = ⊥) : Nat.card D ≤ 5040 := by
  obtain ⟨f,hf,_⟩ := AlternatingSevenNormal.exists_permutation_action C eC
  have hi : Function.Injective f := f.ker_eq_bot_iff.mp (hf.trans hC)
  have hn := Nat.card_le_card_of_injective f hi
  simpa only [Nat.card_perm, Nat.card_fin, Nat.factorial] using hn

omit [Module.Finite (ZMod 2) V] in
theorem overgroup_eq_top_of_marked {J : Subgroup D} (H : Subgroup J)
    (eC : C ≃* alternatingGroup (Fin 7))
    (hC : centralizer (C : Set D) = ⊥)
    (e : H ≃* Equiv.Perm (Fin 7)) : J = ⊤ := by
  have hH : Nat.card H = 5040 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  have hJ : Nat.card J ≤ Nat.card D := Nat.card_le_card_of_injective J.subtype J.subtype_injective
  have hHJ : Nat.card H ≤ Nat.card J := Nat.card_le_card_of_injective H.subtype H.subtype_injective
  have hD := card_le_symmetricSeven C eC hC
  exact eq_top_of_card_eq J (by omega)

omit [Module.Finite (ZMod 2) V] in
noncomputable def full_symmetric_coordinates (H : Subgroup D)
    (eC : C ≃* alternatingGroup (Fin 7))
    (hC : centralizer (C : Set D) = ⊥)
    (e : ActionEquiv (ρ.comp H.subtype) (BinaryPermutation.naturalRepresentation (Fin 7))) :
    ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin 7)) := by
  have hH : Nat.card H = 5040 := by
    rw [Nat.card_congr e.groupEquiv.toEquiv, Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  have hHD : Nat.card H ≤ Nat.card D := Nat.card_le_card_of_injective H.subtype H.subtype_injective
  have hD := card_le_symmetricSeven C eC hC
  have he : H = ⊤ := eq_top_of_card_eq H (by omega)
  let f : H ≃* D := MulEquiv.ofBijective H.subtype ⟨H.subtype_injective, by
    intro d
    exact ⟨⟨d, he ▸ mem_top d⟩, rfl⟩⟩
  refine ⟨f.symm.trans e.groupEquiv, e.linearEquiv, ?_⟩
  intro d v
  have h := e.intertwines (f.symm d) v
  change e.linearEquiv (ρ (f (f.symm d)) v) = _ at h
  simpa only [f.apply_symm_apply, MulEquiv.trans_apply] using h

omit [Finite D] [C.Normal] [Module.Finite (ZMod 2) V] in
theorem symmetric_coordinates_component [Group.IsPerfect C]
    (eC : C ≃* alternatingGroup (Fin 7)) (e : D ≃* Equiv.Perm (Fin 7)) :
    C.map e.toMonoidHom = alternatingGroup (Fin 7) := by
  have hle : C.map e.toMonoidHom ≤ alternatingGroup (Fin 7) := by
    rw [← (commutator_eq_self : ⁅C, C⁆ = C), map_commutator]
    exact (commutator_mono le_top le_top).trans alternatingGroup.commutator_perm_le
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective e.injective, Nat.card_congr eC.toEquiv]

omit [Finite D] in
theorem fixedCodim_eq_moved (U : Subrepresentation ρ)
    (hc : U.toSubmodule ⊔ ρ.invariants = ⊤) (A : Subgroup D) :
    fixedCodim ρ A = fixedCodim U.toRepresentation A := by
  apply ((fixedCodim_subrepresentation_eq_iff ρ U A).mpr ?_).symm
  apply top_unique
  rw [← hc]
  exact sup_le_sup_left (fun v hv a => hv a) _

theorem offender_eq_top_of_seven [IsQuasisimple C] [IsSimpleGroup C]
    (eC : C ≃* alternatingGroup (Fin 7))
    (hC : centralizer (C : Set D) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C)
    (hf : Function.Injective ρ) (hCJ : C ≤ offenderSubgroup ρ) :
    offenderSubgroup ρ = ⊤ := by
  obtain ⟨c⟩ := offender_source_conclusion ρ C hC hsq hf hCJ
  obtain ⟨_, hfaith, _, hm⟩ := classification_marked_rows _
    ((subgroupOfEquivOfLe hCJ).trans eC) c.sectionData c.clause_one
  rcases hm with ⟨H, ⟨e⟩⟩ | hd
  · exact overgroup_eq_top_of_marked C H eC hC e.action.groupEquiv
  · let s := ambientSection ρ C hCJ c.sectionData
    have hc : C = ⊤ := Representation.BinaryAlternatingSevenControl.normal_alternatingSeven_eq_top
      s.action (ambientSection_faithful ρ C hCJ c.sectionData hC hfaith)
      ((ambientSection_finrank ρ C hCJ c.sectionData).trans hd) C eC
    exact top_unique (hc ▸ hCJ)

theorem original_source_conclusion [IsQuasisimple C] [IsSimpleGroup C]
    (eC : C ≃* alternatingGroup (Fin 7))
    (hC : centralizer (C : Set D) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C)
    (hf : Function.Injective ρ) (hCJ : C ≤ offenderSubgroup ρ) :
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ C) := by
  have hfit : generalizedFitting D = C := generalizedFitting_eq_of_quasisimple_centralizer C hC
  have hcore : pCore 2 D = ⊥ := SimpleSocle.pCore_eq_bot (SimpleSocle.radical_eq_bot C hC) 2
  apply SourceB5.classification.quasisimple D V ρ C
  refine ⟨inferInstance, hf, inferInstance, hsq, ?_, hcore,
    offender_eq_top_of_seven ρ C eC hC hsq hf hCJ⟩
  rw [hfit]
  exact (sup_eq_left.mpr (by
    rw [← hfit]
    exact (show center D ≤ fittingSubgroup D from le_sSup ⟨inferInstance,inferInstance⟩).trans
      (fitting_le_generalizedFitting D))).symm

/-- The original moved module, with its actual full actor and fixed complement. -/
structure ActionData where
  sectionData : MovedSection ρ C
  invariant_complement : IsCompl sectionData.space.toSubmodule ρ.invariants
  central_eq_bot : sectionData.central.toSubmodule = ⊥
  irrPlus : IsIrrPlus ρ C sectionData.space.toSubmodule
  faithful_quotient : Function.Injective sectionData.action
  faithful : Function.Injective sectionData.space.toRepresentation
  irreducible : IsIrreducible (sectionData.action.comp C.subtype)
  models : (∃ e : ActionEquiv sectionData.space.toRepresentation
      (BinaryPermutation.naturalRepresentation (Fin 7)),
      C.map e.groupEquiv.toMonoidHom = alternatingGroup (Fin 7)) ∨
    (C = ⊤ ∧ Module.finrank (ZMod 2) sectionData.space.toSubmodule = 4)

omit [Finite D] [Module.Finite (ZMod 2) V] [C.Normal] in
theorem full_moved_faithful (s : MovedSection ρ C) (hf : Function.Injective s.action) :
    Function.Injective s.space.toRepresentation := by
  intro a b hab
  apply hf
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change Submodule.Quotient.mk (s.space.toRepresentation a v) =
      Submodule.Quotient.mk (s.space.toRepresentation b v)
    rw [hab]

theorem actionData_of_source_conclusion [Group.IsPerfect C]
    (eC : C ≃* alternatingGroup (Fin 7))
    (hC : centralizer (C : Set D) = ⊥)
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ C) :
    Nonempty (ActionData ρ C) := by
  obtain ⟨hi, hf, hir, hm⟩ := classification_marked_rows ρ eC c.sectionData c.clause_one
  have hz := source_central_eq_bot ρ eC c
  refine ⟨⟨c.sectionData, source_invariant_split ρ eC c, hz, hi, hf,
    full_moved_faithful ρ C c.sectionData hf, hir, ?_⟩⟩
  rcases hm with ⟨H, ⟨e⟩⟩ | hd
  · let E := full_symmetric_coordinates c.sectionData.action C H eC hC e.action
    let q := (c.sectionData.central.toSubmodule.quotEquivOfEqBot hz).symm
    let F : ActionEquiv c.sectionData.space.toRepresentation
        (BinaryPermutation.naturalRepresentation (Fin 7)) :=
      ⟨E.groupEquiv, q.trans E.linearEquiv, fun g v => E.intertwines g (q v)⟩
    exact Or.inl ⟨F, symmetric_coordinates_component C eC E.groupEquiv⟩
  · exact Or.inr ⟨Representation.BinaryAlternatingSevenControl.normal_alternatingSeven_eq_top
      c.sectionData.action hf hd C eC, full_moved_dimension ρ C c.sectionData hz hd⟩

theorem nonempty_actionData [IsQuasisimple C] [IsSimpleGroup C]
    (eC : C ≃* alternatingGroup (Fin 7))
    (hC : centralizer (C : Set D) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C)
    (hf : Function.Injective ρ) (hCJ : C ≤ offenderSubgroup ρ) :
    Nonempty (ActionData ρ C) := by
  obtain ⟨c⟩ := original_source_conclusion ρ C eC hC hsq hf hCJ
  exact actionData_of_source_conclusion ρ C eC hC c

omit [Finite D] [C.Normal] in
theorem ActionData.fixedCodim_eq (m : ActionData ρ C) (A : Subgroup D) :
    fixedCodim ρ A = fixedCodim m.sectionData.space.toRepresentation A :=
  fixedCodim_eq_moved ρ m.sectionData.space m.invariant_complement.sup_eq_top A

omit [Finite D] [C.Normal] in
theorem ActionData.fixedCodim_natural (m : ActionData ρ C)
    (e : ActionEquiv m.sectionData.space.toRepresentation (BinaryPermutation.naturalRepresentation (Fin 7)))
    (A : Subgroup D) :
    fixedCodim ρ A = fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7))
      (A.map e.groupEquiv.toMonoidHom) := by
  rw [m.fixedCodim_eq ρ C A]
  exact fixedCodim_map_equivariant _ _ e.groupEquiv.toMonoidHom e.linearEquiv e.intertwines A

noncomputable def ActionData.naturalLift (m : ActionData ρ C)
    (e : ActionEquiv m.sectionData.space.toRepresentation (BinaryPermutation.naturalRepresentation (Fin 7))) :
    BinaryPermutation.natural (Fin 7) →ₗ[ZMod 2] V :=
  m.sectionData.space.toSubmodule.subtype.comp e.linearEquiv.symm.toLinearMap

omit [Finite D] [Module.Finite (ZMod 2) V] [C.Normal] in
theorem ActionData.naturalLift_injective (m : ActionData ρ C)
    (e : ActionEquiv m.sectionData.space.toRepresentation (BinaryPermutation.naturalRepresentation (Fin 7))) :
    Function.Injective (m.naturalLift ρ C e) :=
  m.sectionData.space.toSubmodule.subtype_injective.comp e.linearEquiv.symm.injective

omit [Finite D] [Module.Finite (ZMod 2) V] [C.Normal] in
theorem ActionData.naturalLift_intertwines (m : ActionData ρ C)
    (e : ActionEquiv m.sectionData.space.toRepresentation (BinaryPermutation.naturalRepresentation (Fin 7)))
    (g : D) (w : BinaryPermutation.natural (Fin 7)) :
    m.naturalLift ρ C e (BinaryPermutation.naturalRepresentation (Fin 7) (e.groupEquiv g) w) =
      ρ g (m.naturalLift ρ C e w) := by
  have h := e.intertwines g (e.linearEquiv.symm w)
  rw [e.linearEquiv.apply_symm_apply] at h
  have he := congrArg e.linearEquiv.symm h
  rw [e.linearEquiv.symm_apply_apply] at he
  exact (congrArg Subtype.val he).symm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingModels
