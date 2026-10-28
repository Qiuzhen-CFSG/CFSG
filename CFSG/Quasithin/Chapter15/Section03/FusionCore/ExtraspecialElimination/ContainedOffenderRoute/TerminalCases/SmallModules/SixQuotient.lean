module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SmallModules.SectionIdentification
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Selecting the marked six-letter quotient

Strong offending on the original module and its literal moved central quotient
removes all ratio-one rows of the corrected B.5.1/B.4.2 contract. The component
has order 360, which excludes the remaining linear and larger-field rows.
The surviving symplectic-two row has quotient dimension four and an
order-720 offender subgroup. Thus the actor properly contains the component.
The full outer-extension clause selects the six-letter natural action, and
its order-360 component maps onto the actual alternating subgroup.

The late-actor application retains the complete corrected source witness,
including its literal central quotient, for the independent central-cover
recovery. No equality between the actor and the component is assumed.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.4.2,
printed p.86, B.5.1, pp.99--103, and 15.3.49, printed p.1145.
The imported matrix order formulas retain their ATLAS attribution and license.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SmallModules
open ReducedModels ComponentReduction ModelReduction BinaryModels

private theorem sl_card_mul (d : ℕ) [NeZero d] :
    Nat.card SL(d,ZMod 2) = ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) d
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(d,ZMod 2)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  simpa using h

private theorem card_sl_three (F : BinaryField) :
    Nat.card SL(3,F.Carrier) =
      (2 ^ F.degree) ^ 3 * ((2 ^ F.degree) ^ 3 - 1) * ((2 ^ F.degree) ^ 2 - 1) := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(3,F.Carrier))
  rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin] at hc
  exact (hc.trans (Matrix.PSL3.LinearThree.card_projective_mul_scalar F.Carrier)).trans
    (by rw [F.card_eq])

private theorem sl_three_ne_360 {D : Type*} [Group D]
    (F : BinaryField) (e : D ≃* SL(3,F.Carrier)) (hc : Nat.card D = 360) : False := by
  have he := (Nat.card_congr e.toEquiv).symm.trans hc
  have hd : 2 ^ (F.degree * 3) ∣ 360 := by
    rw [← he, card_sl_three, pow_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hn : F.degree < 2 := by
    by_contra! hn
    have h64 : 64 ∣ 360 := (Nat.pow_dvd_pow 2 (show 6 ≤ F.degree * 3 by omega)).trans hd
    norm_num at h64
  have hF : F.degree = 1 := by have := F.degree_pos; omega
  rw [card_sl_three, hF] at he
  norm_num at he

private theorem sp_ne_360 {D : Type*} [Group D]
    (F : BinaryField) (e : D ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
    (hc : Nat.card D = 360) : False := by
  have he := (Nat.card_congr e.toEquiv).symm.trans hc
  have hd : 2 ^ (F.degree * 4) ∣ 360 := by
    rw [← he, Theory.SpecificGroups.SymplecticFour.card_sp, F.card_eq, pow_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hp := F.degree_pos
  have h16 : 16 ∣ 360 := (Nat.pow_dvd_pow 2 (show 4 ≤ F.degree * 4 by omega)).trans hd
  norm_num at h16

private theorem sl_binary_ne_360 {D : Type*} [Group D]
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : D ≃* SL(d,ZMod 2))
    (hc : Nat.card D = 360) : False := by
  have he := (Nat.card_congr e.toEquiv).symm.trans hc
  rcases hd with rfl | rfl <;> rw [sl_card_mul] at he <;>
    norm_num [Fin.prod_univ_succ] at he

private theorem symplectic_two_of_case {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {J P : Subgroup D}
    (hc : Nat.card J = 360) (hq : quadraticRatio ρ ≠ 1)
    (h : ProjectiveLine.IrreducibleActionCase ρ J P) :
    Nonempty (MarkedActionEquiv ρ P J (symplecticNatural (k := ZMod 2) 2)
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) := by
  cases h with
  | linearTwo _ _ _ _ hr => exact (hq hr).elim
  | linearThree F _ a _ => exact (sl_three_ne_360 F a.groupEquiv hc).elim
  | symplectic F _ _ a _ => exact (sp_ne_360 F a.groupEquiv hc).elim
  | symplecticTwo a _ => exact ⟨a⟩
  | g2 _ _ _ _ _ hr => exact (hq hr).elim
  | g2Two _ _ hr => exact (hq hr).elim
  | symmetric _ _ _ _ hr => exact (hq hr).elim
  | alternatingSix _ _ _ hr => exact (hq hr).elim
  | alternatingSeven _ _ _ _ _ hr => exact (hq hr).elim
  | tripleSix _ _ hr => exact (hq hr).elim
  | binaryLinear d hd _ a _ => exact (sl_binary_ne_360 hd a.groupEquiv hc).elim
  | orthogonalSix _ _ _ _ hr => exact (hq hr).elim
  | symmetricEight _ a _ =>
    have he := (Nat.card_congr a.subgroupEquiv.toEquiv).symm.trans hc
    rw [nat_card_alternatingGroup, Nat.card_fin] at he
    norm_num [Nat.factorial] at he
  | exteriorFive _ _ _ _ _ hr => exact (hq hr).elim

private theorem marked_symmetric_six {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {J P : Subgroup D}
    (hc : Nat.card J = 360)
    (e : MarkedActionEquiv ρ P J (symplecticNatural (k := ZMod 2) 2)
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))))
    (hext : J = ⊤ ∨ (∀ T : Sylow 2 D, J ⊔ (T : Subgroup D) = ⊤) ∧
      OuterNaturalAction ρ) :
    ∃ a : ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin 6)),
      J.map a.groupEquiv.toMonoidHom = alternatingGroup (Fin 6) := by
  have hp : Nat.card P = 720 :=
    (Nat.card_congr e.action.groupEquiv.toEquiv).trans
      Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two
  have hd : Module.finrank (ZMod 2) W = 4 := by
    rw [e.action.linearEquiv.finrank_eq]
    simp
  have hpd := P.card_subgroup_dvd_card
  rw [hp] at hpd
  have ho : OuterNaturalAction ρ := by
    rcases hext with ht | ⟨_, ho⟩
    · have htD : Nat.card D = 360 := by simpa only [ht, Subgroup.card_top] using hc
      rw [htD] at hpd
      norm_num at hpd
    · exact ho
  have hn : IsSymmetricNatural ρ 6 := by
    rcases ho with ⟨n, hn, hN, ⟨a⟩⟩ | ⟨a⟩
    · have ha := a.linearEquiv.finrank_eq
      rw [hd] at ha
      interval_cases n
      · have hD := Nat.card_congr a.groupEquiv.toEquiv
        norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hD
        rw [hD] at hpd
        norm_num at hpd
      · exact ⟨a⟩
      · rw [BinaryPermutation.finrank_natural_odd (Fin 7) (by decide)] at ha
        norm_num at ha
      · rw [BinaryPermutation.finrank_natural_even (Fin 8) (by decide)] at ha
        norm_num at ha
    · obtain ⟨a⟩ := a
      have ha := a.linearEquiv.finrank_eq
      rw [hd, Atlas.G2.Natural.finrank_space] at ha
      omega
  obtain ⟨a⟩ := hn
  refine ⟨a, Equiv.Perm.eq_alternatingGroup_of_index_eq_two ?_⟩
  have hm := (J.map a.groupEquiv.toMonoidHom).card_mul_index
  rw [Subgroup.card_map_of_injective a.groupEquiv.injective, hc] at hm
  have hS : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [hS] at hm
  omega

universe u v
/-- The full corrected B.5.1 contract and the actual strong offender select
an irreducible-plus moved space and the marked S₆ natural quotient action.
In particular this refines the A₆/S₆ alternative without assuming either
actor identification or coordinates on the original module. -/
theorem six_quotient_of_source {D : Type u} [Group D] [Finite D]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D} {κ : GroupClass.{u}}
    (h : QuasisimpleSourceHypothesis ρ κ J)
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ J)
    (e : J ≃* alternatingGroup (Fin 6)) (hs : IsStrongFFModule ρ) :
    IsIrrPlus ρ J c.sectionData.space.toSubmodule ∧
      ∃ a : ActionEquiv c.sectionData.action
          (BinaryPermutation.naturalRepresentation (Fin 6)),
        J.map a.groupEquiv.toMonoidHom = alternatingGroup (Fin 6) := by
  let := h.finite_module
  have hc : Nat.card J = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hq : quadraticRatio ρ ≠ 1 := ne_of_lt
    ((isStrongFFModule_iff_quadraticRatio_lt_one ρ).mp hs)
  have hsq : quadraticRatio c.sectionData.action ≠ 1 := by
    apply ne_of_lt
    apply (isStrongFFModule_iff_quadraticRatio_lt_one _).mp
    obtain ⟨A, hA⟩ := hs
    exact ⟨A, hA.1, (NaturalSelection.movedSection_codim_le c.sectionData A).trans_lt hA.2⟩
  cases c.clause_one with
  | doubleThree _ _ _ _ hr => exact (hq hr).elim
  | naturalDual d hd _ ha =>
    obtain ⟨a⟩ := ha
    exact (sl_binary_ne_360 hd a.groupEquiv hc).elim
  | repeatedNatural d _ hd _ _ _ ha =>
    obtain ⟨a⟩ := ha
    exact (sl_binary_ne_360 hd a.groupEquiv hc).elim
  | irreducible hi _ _ hcase hext =>
    obtain ⟨a⟩ := symplectic_two_of_case hc hsq hcase
    exact ⟨hi, marked_symmetric_six hc a hext⟩

variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper)

/-- Apply the selection to the actual late actor and retain the full source
witness for central-cover recovery. The component equivalence is transported
through its proved relative containment, and strong offending comes from the
same later selected subgroup. -/
theorem six_quotient_on_late_actor (s : StrongPlacement r)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ)
    (e : starImage H L ≃* alternatingGroup (Fin 6)) :
    ∃ c : ProjectiveLine.QuasisimpleSourceConclusion
        (r.placed.action.representation.comp (lateActor r.placed.action).subtype)
        ((starImage H L).subgroupOf (lateActor r.placed.action)),
      IsIrrPlus (r.placed.action.representation.comp (lateActor r.placed.action).subtype)
          ((starImage H L).subgroupOf (lateActor r.placed.action))
          c.sectionData.space.toSubmodule ∧
        ∃ a : ActionEquiv c.sectionData.action
            (BinaryPermutation.naturalRepresentation (Fin 6)),
          ((starImage H L).subgroupOf (lateActor r.placed.action)).map
            a.groupEquiv.toMonoidHom = alternatingGroup (Fin 6) := by
  obtain ⟨c⟩ := r.late_source_conclusion sections orbits source
  exact ⟨c, six_quotient_of_source (r.late_source_hypothesis sections orbits) c
    ((subgroupOfEquivOfLe (r.component_le_late_actor sections orbits)).trans e)
    ⟨_, s.late_offender.2.2⟩⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SmallModules
