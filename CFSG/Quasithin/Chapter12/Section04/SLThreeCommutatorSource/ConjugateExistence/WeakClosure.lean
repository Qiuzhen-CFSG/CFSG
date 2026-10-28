module

public import CFSG.Quasithin.ChapterE.Section03.Parameters
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Core.Lifting
public import CFSG.Quasithin.ChapterE.Section04.Basic
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The weak-closure branch of original 12.4.1

A conjugate of V acting nontrivially on an elementary local module U would,
when a(H/C_H(U),U) ≤ 1, have a hyperplane with a larger fixed space. Lift
that hyperplane through the literal induced automizer. E.3.6 and s(G,V)>1
force its centralizer in U to equal the centralizer of the whole conjugate,
a contradiction. Applying this to every generator gives W₀(T,V) ≤ O₂(H).

The local action bound and centralizer-core containment remain explicit;
SourceInputs records their precise original-source producer obligation.
Source: Aschbacher–Smith, 12.4.1, printed p.812, using E.3.6 and E.3.10.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- E.3.10 on a second local module: an ambient conjugate of V cannot act
nontrivially on a module of local parameter at most one when s(G,V)>1. -/
theorem conjugate_centralizes_of_parameter_bound
    (V U H : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]
    (hHN : H ≤ normalizer (U : Set G))
    (ha : moduleA ((automizerRepresentation U).comp
      (inducedAutomizer U H).subtype) ≤ 1)
    (hs : 1 < globalS V) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ H) :
    V.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAN : A ≤ normalizer (U : Set G) := hg.trans hHN
  let I := inducedAutomizer U H
  have hAI : inducedAutomizer U A ≤ I := map_mono (comap_mono hg)
  let J := (inducedAutomizer U A).subgroupOf I
  have hJmap : J.map I.subtype = inducedAutomizer U A :=
    map_subgroupOf_eq_of_le hAI
  let _ : IsElementaryAbelian 2 (inducedAutomizer U A) :=
    inducedAutomizer_elementary U A hAN
  let _ : IsElementaryAbelian 2 J :=
    IsElementaryAbelian.comap_of_injective I.subtype I.subtype_injective _
  by_contra hn
  have hJne : J ≠ ⊥ := by
    intro he
    apply hn
    apply (inducedAutomizer_eq_bot_iff hAN).mp
    rw [← hJmap, he, Subgroup.map_bot]
  obtain ⟨B, hBJ, hidx, hlt⟩ :=
    exists_hyperplane_fixedSpace_lt_of_moduleA_le_one _ ha ⟨hJne, inferInstance⟩
  obtain ⟨C, hCA, hCI, hcor⟩ := core_lift_image_subgroup hAN (B.map I.subtype)
    (by rw [← hJmap]; exact map_mono hBJ)
  have hcor' : subgroupCorank A C = 1 := by
    rw [hcor, ← hJmap, relIndex_map_map_of_injective _ _ I.subtype_injective]
    exact hidx
  have hr : (subgroupCorank A C : ℕ∞) < globalS A := by
    rw [hcor', globalS_map_equiv]
    exact hs
  have heq := centralizer_inf_eq_of_corank_lt_globalS hCA hr
    (IsElementaryAbelian.isPGroup 2 U)
  apply hlt.ne
  rw [fixedSpace_comp_map, fixedSpace_comp_map, hJmap, ← hCI]
  ext v
  rw [mem_fixedSpace_inducedAutomizer U A hAN,
    mem_fixedSpace_inducedAutomizer U C (hCA.trans hAN)]
  have he := congrArg (fun W : Subgroup G => (v.toMul : G) ∈ W) heq
  simpa only [mem_inf, v.toMul.property, true_and] using (iff_of_eq he).symm

/-- The weak closure in the original ambient group lies in the second
two-core once its literal module has parameter at most one. -/
theorem weakClosure_le_core_of_parameter_bound
    (V U H T : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]
    (hTH : T ≤ H) (hHN : H ≤ normalizer (U : Set G))
    (hcore : H ⊓ centralizer (U : Set G) ≤ H.pCoreIn 2)
    (ha : moduleA ((automizerRepresentation U).comp
      (inducedAutomizer U H).subtype) ≤ 1)
    (hs : 1 < globalS V) : indexedWeakClosure V T 0 ≤ H.pCoreIn 2 := by
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g, rfl, hg⟩ := (mem_gamma_zero_iff V T A).mp hA
  exact (le_inf (hg.trans hTH)
    (conjugate_centralizes_of_parameter_bound V U H hHN ha hs g
      (hg.trans hTH))).trans hcore

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
