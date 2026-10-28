module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.QuotientAction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.SourceCatalogue
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.SectionOffender

/-!
# The complete corrected B.4.2 classification on the actual LT action

Conjugacy puts an original offender in any chosen Sylow two-subgroup.
Fixed-codimension inequalities on the moved central section then supply
an offender, and finite minimization supplies a best offender for LT.
Together with the proved local group reductions and quotient faithfulness,
this discharges every hypothesis of the complete corrected B.4.2 input.
If LA=G, the same argument directly classifies the original ambient action,
retaining all group and linear markings and every offender clause.

Parameters: the complete universal ProjectiveLine.IrreducibleClassificationInput
and ContainsSimpleTwoGroups K. The former is the genuine earlier B.4.2
implication for the source assembly owner to discharge; the latter is the
precise class condition for SQTK inheritance. No B.5.1 conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed p.99, and B.1.5(8), pp.69–70.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Offender generation supplies an original best offender inside every Sylow two-subgroup. -/
theorem bestOffender_in_sylow [Finite G] [Nontrivial G]
    (hj : offenderSubgroup ρ = ⊤) (T : Sylow 2 G) :
    ∃ A ≤ (T : Subgroup G), IsBestOffender ρ A := by
  have hex : ∃ A, IsBestOffender ρ A := by
    by_contra hn
    have hb : offenderSubgroup ρ = ⊥ := by
      apply bot_unique
      exact iSup₂_le fun A hA => (hn ⟨A, hA.1⟩).elim
    exact top_ne_bot (hj.symm.trans hb)
  obtain ⟨A, hA⟩ := hex
  let := hA.1.2
  obtain ⟨P, hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P T
  have hPT : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = T :=
    congrArg Sylow.toSubgroup hg
  exact ⟨A.map (MulAut.conj g).toMonoidHom,
    hPT ▸ Subgroup.map_mono hAP, hA.map_conj ρ g⟩

/-- Passing to the moved central section cannot increase fixed codimension. -/
theorem moved_fixedCodim_le [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ L) (A : Subgroup G) :
    fixedCodim s.action A ≤ fixedCodim ρ A := by
  exact (Nat.le_add_right _ _).trans
    ((fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A).trans
      (fixedCodim_subrepresentation_le ρ s.space A))

/-- An original offender remains an offender for the unchanged actor on the quotient. -/
theorem moved_offender [FiniteDimensional (ZMod 2) V] (s : MovedSection ρ L)
    {A : Subgroup G} (hA : IsOffender ρ A) : IsOffender s.action A :=
  ⟨hA.1, (moved_fixedCodim_le s A).trans hA.2⟩

/-- The literal LT quotient action has a best offender, derived from the original action. -/
theorem local_bestOffender [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) (T : Sylow 2 G) :
    ∃ B, IsBestOffender (s.action.comp (L ⊔ (T : Subgroup G)).subtype) B := by
  let := h.finite_module
  let := h.quasisimple
  let : Nontrivial (L ⧸ center L) := h.quasisimple.simple.toNontrivial
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  let : Nontrivial G := L.subtype_injective.nontrivial
  obtain ⟨A, hAT, hA⟩ := bestOffender_in_sylow h.generated T
  obtain ⟨B, hBA, hB⟩ := (moved_offender s (hA.isOffender ρ)).exists_bestOffender s.action
  exact ⟨B.subgroupOf (L ⊔ (T : Subgroup G)),
    hB.subgroupOf s.action (hBA.trans (hAT.trans le_sup_right))⟩

/-- The quotient action is irreducible on the actual F*(LA). -/
theorem local_irreducible [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hI : IsIrrPlus ρ L s.space.toSubmodule) (A : Subgroup G) (hA : IsPGroup 2 A) :
    IsIrreducible ((s.action.comp (L ⊔ A).subtype).comp
      (generalizedFitting ↥(L ⊔ A)).subtype) := by
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  rw [local_generalizedFitting L A h.fitting h.twoCore hA]
  exact RepEquiv.irreducible_of_group_iso
    (subgroupOfEquivOfLe (show L ≤ L ⊔ A from le_sup_left)).symm
    (fun _ _ => rfl) (moved_action_irreducible s hI)

/-- Apply the complete source-correct B.4.2 implication to the actual LT action. -/
theorem local_classification [Finite G] {K : CFSG.Quasithin.GroupClass}
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u, v} K)
    (hK : ContainsSimpleTwoGroups K)
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hI : IsIrrPlus ρ L s.space.toSubmodule) (T : Sylow 2 G) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase
      (s.action.comp (L ⊔ (T : Subgroup G)).subtype)
      (generalizedFitting ↥(L ⊔ (T : Subgroup G)))
      (offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype)) := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  have hF : IsQuasisimple (generalizedFitting ↥(L ⊔ (T : Subgroup G))) := by
    rw [local_generalizedFitting L T h.fitting h.twoCore T.isPGroup']
    exact IsQuasisimple.of_mulEquiv
      (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm
  exact earlier _ _ _ (local_sqtk hK L T h.sqtk T.isPGroup') hF
    (local_faithful h s T T.isPGroup') (local_irreducible h s hI T T.isPGroup')
    (local_bestOffender h s T)

/-- Once LA is all of G, recover F*(G)=L, ambient faithfulness and the full corrected catalogue. -/
theorem ambient_classification_of_local_eq_top [Finite G]
    {K : CFSG.Quasithin.GroupClass}
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u, v} K)
    (hK : ContainsSimpleTwoGroups K)
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hI : IsIrrPlus ρ L s.space.toSubmodule) (A : Subgroup G) (hA : IsPGroup 2 A)
    (htop : L ⊔ A = ⊤) :
    L = generalizedFitting G ∧ Function.Injective s.action ∧
      SourceInduction.ProjectiveLine.IrreducibleActionCase s.action L
        (offenderSubgroup s.action) := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  have hquot := isPGroup_quotient_of_sup_eq_top L A hA htop
  have hfit : generalizedFitting G = L :=
    generalizedFitting_eq_of_quasisimple_two_quotient L hquot h.twoCore
  have hfaith : Function.Injective s.action := by
    have hf := local_faithful h s A hA
    rw [htop] at hf
    intro x y hxy
    exact congrArg (fun g : (⊤ : Subgroup G) => (g : G))
      (hf (show s.action.comp (⊤ : Subgroup G).subtype ⟨x, mem_top x⟩ =
        s.action.comp (⊤ : Subgroup G).subtype ⟨y, mem_top y⟩ from hxy))
  have hsqtk := sqtk_of_twoGroup_quotient hK L hquot h.sqtk
  have hF : IsQuasisimple (generalizedFitting G) := hfit.symm ▸ h.quasisimple
  have hirr : IsIrreducible (s.action.comp (generalizedFitting G).subtype) := by
    rw [hfit]
    exact moved_action_irreducible s hI
  have hbest : ∃ B, IsBestOffender s.action B := by
    let T : Sylow 2 G := Classical.choice inferInstance
    obtain ⟨B, hB⟩ := local_bestOffender h s T
    let σ := s.action.comp (L ⊔ (T : Subgroup G)).subtype
    have ho := (hB.isOffender σ).map_equivariant σ s.action
      (L ⊔ (T : Subgroup G)).subtype Subtype.val_injective (LinearEquiv.refl _ _)
      (fun _ _ => rfl)
    obtain ⟨C, _, hC⟩ := ho.exists_bestOffender s.action
    exact ⟨C, hC⟩
  refine ⟨hfit.symm, hfaith, ?_⟩
  simpa only [hfit] using earlier G _ s.action hsqtk hF hfaith hirr hbest

end CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
