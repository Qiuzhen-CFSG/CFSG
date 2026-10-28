module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M24Table.Transport
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms
public import Theory.GroupTheory.GeneralizedFitting.SolvableNormalKernel

/-!
# Assembly of the M₂₄ involution table from marked centralizers

Every involutory automorphism is inner, and its fixed subgroup is proved
isomorphic to one of the two marked full centralizers. Transport of the exact
kernel and quotient presentations reduces the table to the two representative
calculations. A normal self-centralizing two-subgroup in each representative
centralizer also excludes all components after transport.

The shape and kernel-action premises below remain explicit obligations. This
module does not yet claim the unconditional source table.

Source: Aschbacher–Smith 16.1.5(7) and its use in 16.1.7, printed pp.1171–1173;
Notation E.2.16 on printed p.228 defines the dihedral central product.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24InvolutionCentralizers Theory.GroupTheory

/-- The two exact representative calculations suffice; involution coverage and
innerness are discharged for the actual carrier. -/
theorem m24_involution_alternative_of_representatives
    (hA : IsM24DihedralExtension centralizer2A)
    (hB : Nonempty (GroupExtension (Elementary 6) centralizer2B S5))
    (r : MulAut M24) (hr : orderOf r = 2) : M24InvolutionAlternative r := by
  obtain ⟨hi, he⟩ := fixedSubgroup_alternative r hr
  refine ⟨hi, ?_⟩
  rcases he with ⟨e⟩ | ⟨e⟩
  all_goals rcases e with ⟨e⟩
  · exact Or.inl (hA.map e.symm)
  · exact Or.inr (hB.map (fun s => extensionTransport s e.symm))

/-- A normal self-centralizing two-subgroup excludes components of its group. -/
theorem m24_no_component_of_kernel {C : Type*} [Group C] [Finite C]
    (h : ∃ Q : Subgroup C, Q.Normal ∧ IsPGroup 2 Q ∧ centralizer (Q : Set C) ≤ Q)
    (K : Subgroup C) : ¬ IsComponent C K := by
  obtain ⟨Q, hn, hp, hc⟩ := h
  let := hn
  let : Group.IsNilpotent Q := hp.isNilpotent
  exact not_isComponent_of_solvable_normal_selfCentralizing Q hc K

/-- Once the two actual kernel actions are computed, every involutory fixed
subgroup is component-free. No solvability of L₃(2) or S₅ is asserted. -/
theorem m24_no_component_of_representative_kernels
    (hA : ∃ Q : Subgroup centralizer2A,
      Q.Normal ∧ IsPGroup 2 Q ∧ centralizer (Q : Set centralizer2A) ≤ Q)
    (hB : ∃ Q : Subgroup centralizer2B,
      Q.Normal ∧ IsPGroup 2 Q ∧ centralizer (Q : Set centralizer2B) ≤ Q)
    (r : MulAut M24) (hr : orderOf r = 2) (K : Subgroup r.fixedSubgroup) :
    ¬ IsComponent r.fixedSubgroup K := by
  intro hK
  rcases (fixedSubgroup_alternative r hr).2 with ⟨e⟩ | ⟨e⟩
  all_goals rcases e with ⟨e⟩
  · exact m24_no_component_of_kernel hA _ (hK.map_equiv e)
  · exact m24_no_component_of_kernel hB _ (hK.map_equiv e)

end CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
