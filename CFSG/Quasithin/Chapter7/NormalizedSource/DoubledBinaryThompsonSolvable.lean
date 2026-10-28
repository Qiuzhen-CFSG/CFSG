module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCubicFactors
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# The solvable Thompson alternatives in the paired-plane argument

In a finite solvable group with trivial two-core, a nontrivial elementary
two-subgroup cannot centralize the Fitting subgroup: self-centralization
puts it in F, and nilpotence then puts it in O₂. Consequently an equal-weight
minimal subgroup of every best offender contributes a B.1.9 plane factor.
The centralizing best-offender factor has trivial intersection with these
plane factors, so it vanishes and the plane factors generate all offenders.

For the actual Thompson image, the previously proved full-preimage
containment would therefore put the whole original Thompson subgroup in M
if its image were solvable. This excludes both the single and multiple S₃
alternatives. The chosen-module application is in
NonFFSourceDoubledBinaryThompsonSolvable.
Source: Aschbacher–Smith, proof of 7.7.3, printed p.707; B.1.9, pp.71–72,
refs/quasithin.pdf. The nonsolvable branches and final assembly remain with
qt-d-1222-nonff-doubled.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonSolvable
open ChapterB.FittingStructure

/-- In a solvable group with trivial two-core, no nontrivial elementary
two-subgroup centralizes the Fitting subgroup. -/
private theorem elementary_not_centralizing_fitting
    {D : Type*} [Group D] [Finite D]
    (hs : Group.IsSolvable D) (hcore : pCore 2 D = ⊥)
    (A : Subgroup D) (hA : IsElementaryTwo A) :
    ⁅fittingSubgroup D,A⁆ ≠ ⊥ := by
  intro hz
  have hAF : A ≤ fittingSubgroup D :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)).trans
      (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs)
  let := hA.2
  have hp : IsPGroup 2 (A.subgroupOf (fittingSubgroup D)) :=
    (IsElementaryAbelian.isPGroup 2 A).comap_subtype
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hm := map_mono (f := (fittingSubgroup D).subtype) hS
  rw [map_subgroupOf_eq_of_le hAF] at hm
  have hh := hm.trans (S.map_le_pCore inferInstance inferInstance 2)
  exact hA.1 (le_bot_iff.mp (hh.trans_eq hcore))

/-- In the solvable case the B.1.9 symmetric-three factors generate the
whole offender subgroup. The centralizing best-offender factor is trivial. -/
theorem solvable_offenderSubgroup_eq_planeGenerated
    {D X : Type*} [Group D] [Finite D] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) D X) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) (hs : Group.IsSolvable D) :
    offenderSubgroup ρ = planeGenerated ρ := by
  have hl := localPlaneLaw ρ hf hcore
  have hz : centralizingBestGenerated ρ = ⊥ := by
    apply le_bot_iff.mp
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA,hAC⟩
    obtain ⟨B,hB,hBA⟩ := hA.exists_minimal ρ
    have hn := elementary_not_centralizing_fitting hs hcore B hB.1.1
    have hBE : B ≤ planeGenerated ρ :=
      (offender_le_planeGroup ρ ⟨hB,hn,rfl⟩).trans
        (BestOffenderNormalization.planeGroup_le_planeGenerated ρ ⟨B,hB,hn,rfl⟩)
    have hBC : B ≤ centralizingBestGenerated ρ :=
      hBA.1.trans (le_iSup_of_le A (le_iSup_of_le ⟨hA,hAC⟩ le_rfl))
    have hh := (le_inf hBE hBC).trans_eq
      (planeGenerated_inf_centralizingBestGenerated_eq_bot ρ hf hl)
    exact (hB.1.1.1 (le_bot_iff.mp hh)).elim
  rw [offenderSubgroup_eq_planeGenerated_sup_centralizingBestGenerated ρ hf hcore hl,hz,sup_bot_eq]

open Stellmacher ChapterB.InternalThompsonAction DoubledBinaryThompson

/-- Containment of the actual symmetric-factor preimages excludes a solvable
Thompson image whenever the original Thompson subgroup escapes M. -/
theorem no_solvable_thompson
    {H : Type*} [Group H] [Finite H]
    (Y : Subgroup H) [Y.Normal] [IsElementaryAbelian 2 Y]
    (M : Subgroup H) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hcore : pCore 2 (ActionQuotient Y) = ⊥)
    (hnot : ¬ elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ M)
    (hplanes : ((planeGenerated (thompsonAction Y)).map
      (thompsonImage Y).subtype).comap (actionMk Y) ≤ M) :
    ¬ Group.IsSolvable (thompsonImage Y) := by
  intro hs
  have h := thompson_hypothesis Y hH hcore
  rw [← solvable_offenderSubgroup_eq_planeGenerated (thompsonAction Y)
    h.faithful h.twoCore hs,h.generated,← MonoidHom.range_eq_map,range_subtype] at hplanes
  exact hnot (fun x hx => hplanes (mem_map_of_mem (actionMk Y) hx))

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonSolvable
