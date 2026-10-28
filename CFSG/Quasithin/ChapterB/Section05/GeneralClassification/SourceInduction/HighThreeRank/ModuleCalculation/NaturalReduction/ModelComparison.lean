module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.Applicability
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.Sections
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.KernelObstruction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.AlternatingEight
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity

/-!
# Comparing the full B.5.1 action in the high-three-rank branch

A nontrivial normal perfect subgroup maps to the alternating subgroup under
any isomorphism to a symmetric group of degree at least five. The analogous
fact for the actual octonion group identifies its derived subgroup. Thus the
full actor equivalence supplied by B.5.1(1i) also supplies the required marking;
the module equivalence and the marking use exactly the same group map.

The five-point case is excluded by the original component's three-rank.
The actual lifted component has center divisible by three. The constructed
universal double cover excludes A₈, and the complete earlier multiplier table
I.1.3 excludes G₂(2)′. `reduced_of_earlier_source` assembles these exclusions
with the full B.5.1 alternative to construct the exact `ReducedSymmetricModel`.
The earlier conditional comparison and perfect-cover interfaces are preserved.

The universal earlier-source parameters are the complete
`ProjectiveLine.QuasisimpleClassificationInput`, produced by
`qt-b05-quasisimple`, and `BinaryG2Exclusion.EarlierMultiplierInput`, the
complete I.1.3 implication produced by `qt-i-01` (including `qt-i01-lie-a2`).
The supplied `NoncentralContext` is the task's explicit input. Its earlier
B.5.2/B.5.5 contracts remain in `CoverCentralizer.SourceConstruction.LowerSources`,
with producer `qt-b05-quotient-components`; no new copy or parameter is needed
here. The final theorem assumes neither a component exclusion nor
`ThreeFreePerfectKernels`. Discharge of the universal source inputs and the
moved-module extension remains with the parent assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.1,
printed pp.99–103, and the lifted-component comparison in B.5.7, p.106.
The kernel route uses the covering convention and complete multiplier table
of I.1.1 and I.1.3, p.407.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison
open QuasisimpleSource
universe u v w z
variable {D : Type u} [Group D]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) D V}

private theorem perfect_map_le_derived {E : Type w} [Group E]
    (L : Subgroup D) [Group.IsPerfect L] (e : D ≃* E) :
    L.map e.toMonoidHom ≤ commutator E := by
  let : Group.IsPerfect (L.map e.toMonoidHom) := Group.IsPerfect.map _
  rw [← Subgroup.commutator_eq_self (H := L.map e.toMonoidHom)]
  exact commutator_mono le_top le_top

/-- A normal nontrivial perfect subgroup is the marked alternating subgroup
under any symmetric-group isomorphism. -/
theorem symmetric_component_image (L : Subgroup D) [L.Normal]
    [Group.IsPerfect L] [Nontrivial L] {n : ℕ} (hn : 5 ≤ n)
    (e : D ≃* Equiv.Perm (Fin n)) :
    L.map e.toMonoidHom = alternatingGroup (Fin n) := by
  let : (L.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ e.surjective
  have hn' : 5 ≤ Nat.card (Fin n) := by simpa using hn
  refine le_antisymm ?_ (Equiv.Perm.alternatingGroup_le_of_normal hn'
    ((L.equivMapOfInjective e.toMonoidHom e.injective).injective.nontrivial))
  rw [← alternatingGroup.commutator_perm_eq hn']
  exact perfect_map_le_derived L e

/-- Construct both markings from one actor equivalence. -/
noncomputable def markAction {E : Type w} [Group E]
    {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) E W} (L : Subgroup D) (M : Subgroup E)
    (e : ActionEquiv ρ σ) (he : L.map e.groupEquiv.toMonoidHom = M) :
    MarkedActionEquiv ρ ⊤ L σ M where
  action := {
    groupEquiv := Subgroup.topEquiv.trans e.groupEquiv
    linearEquiv := e.linearEquiv
    intertwines g v := e.intertwines g.val v }
  contained := le_top
  subgroupEquiv := (L.equivMapOfInjective e.groupEquiv.toMonoidHom e.groupEquiv.injective).trans
    (MulEquiv.subgroupCongr he)
  compatible _ := rfl

/-- The actor equivalence in a natural symmetric action also marks its component. -/
noncomputable def markSymmetric (L : Subgroup D) [L.Normal]
    [Group.IsPerfect L] [Nontrivial L] {n : ℕ} (hn : 5 ≤ n)
    (e : ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin n))) :
    MarkedActionEquiv ρ ⊤ L (BinaryPermutation.naturalRepresentation (Fin n))
      (alternatingGroup (Fin n)) :=
  markAction L _ e (symmetric_component_image L hn e.groupEquiv)

/-- The derived binary octonion group is the marked component. -/
theorem g2_component_image (L : Subgroup D) [L.Normal]
    [Group.IsPerfect L] [Nontrivial L] (e : D ≃* Atlas.G2.Model (ZMod 2)) :
    L.map e.toMonoidHom = commutator (Atlas.G2.Model (ZMod 2)) := by
  let : (L.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ e.surjective
  refine le_antisymm (perfect_map_le_derived L e) ?_
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
  apply Atlas.G2.BinaryException.H_le_normal
  let : Nontrivial (L.map e.toMonoidHom) :=
    (L.equivMapOfInjective e.toMonoidHom e.injective).injective.nontrivial
  exact (L.map e.toMonoidHom).nontrivial_iff_ne_bot.mp inferInstance

/-- Rank at least two is incompatible with the five-point component. -/
theorem not_alternatingFive [Finite D] (hr : 1 < primeRank 3 D)
    (e : D ≃* alternatingGroup (Fin 5)) : False := by
  obtain ⟨E, hE, hc⟩ := exists_elementary_nine_of_three_rank (by omega : 2 ≤ primeRank 3 D)
  have hd := card_subgroup_dvd_card E
  rw [hc, Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hd
  norm_num at hd
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

private theorem center_eq_bot_of_perfect_simple (M : Type w) [Group M]
    [IsSimpleGroup M] [Group.IsPerfect M] : center M = ⊥ := by
  rcases (inferInstance : (center M).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative M (center_eq_top_iff.mp ht)).elim

/-- The full B.5.1 quotient action, retaining all source clauses, reduces to
six or seven once the two remaining intrinsic component exclusions are proved. -/
theorem reduced_of_component_exclusions
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (ρ : Representation (ZMod 2) G V) (hyp : FFHypothesis K ρ)
    {L : Subgroup G} (hL : IsComponent G L) (hr : 1 < primeRank 3 L)
    (d : NoncentralContext K G L) {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hm : ¬ A ≤ centralizer (pCore 3 G : Set G))
    (h8 : ¬ Nonempty (L ≃* alternatingGroup (Fin 8)))
    (hg : ¬ Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    Nonempty (ReducedSymmetricModel ρ L A) := by
  have hout : ¬ A ≤ L := fun h => hm (h.trans
    (le_centralizer_iff.mp (CoverCentralizer.threeCore_centralizes_component hL)))
  obtain ⟨c⟩ := local_classification ρ earlier hyp hL d hA
  obtain ⟨_, _, _, _, _, ho⟩ := local_irreducible ρ hout c
  let J := L.subgroupOf (L ⊔ A)
  let : L.Normal := d.normal
  let : J.Normal := inferInstance
  let : IsQuasisimple J := (hL.subgroupOf le_sup_left).2
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  let : Nontrivial J := (QuotientGroup.mk'_surjective (center J)).nontrivial
  let r : J ≃* L := subgroupOfEquivOfLe (show L ≤ L ⊔ A from le_sup_left)
  unfold OuterNaturalAction at ho
  rcases ho with hs | hge
  · obtain ⟨n, hn, hn', ⟨e⟩⟩ := hs
    let em := markSymmetric J hn e
    let eL := r.symm.trans em.subgroupEquiv
    have h5 : n ≠ 5 := by
      rintro rfl
      exact not_alternatingFive hr eL
    have hne8 : n ≠ 8 := by
      rintro rfl
      exact h8 ⟨eL⟩
    exact ⟨c, n, by omega, ⟨em⟩⟩
  · obtain ⟨e⟩ := hge
    have he := g2_component_image J e.groupEquiv
    let eL := r.symm.trans ((J.equivMapOfInjective e.groupEquiv.toMonoidHom
      e.groupEquiv.injective).trans (MulEquiv.subgroupCongr he))
    exact (hg ⟨eL⟩).elim

/-- Application to the actual lifted component. Only the two concrete perfect-cover
kernel calculations remain beyond the allowed complete B.5.1 source input. -/
theorem reduced_of_threeFreePerfectKernels
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h8 : ThreeFreePerfectKernels.{u} (alternatingGroup (Fin 8)))
    (hg : ThreeFreePerfectKernels.{u} (commutator (Atlas.G2.Model (ZMod 2))))
    (ρ : Representation (ZMod 2) G V) (hyp : FFHypothesis K ρ)
    {L : Subgroup G} (hL : IsComponent G L) (hr : 1 < primeRank 3 L)
    (d : NoncentralContext K G L) {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hm : ¬ A ≤ centralizer (pCore 3 G : Set G)) :
    Nonempty (ReducedSymmetricModel ρ L A) := by
  apply reduced_of_component_exclusions earlier ρ hyp hL hr d hA hm
  · rintro ⟨e⟩
    exact not_model_of_threeFreePerfectKernels hL d
      (alternatingGroup.center_eq_bot (by simp)) h8 e
  · rintro ⟨e⟩
    let := hL.2
    let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
      Atlas.G2.isSimple_commutator_binary
    exact not_model_of_threeFreePerfectKernels hL d
      (center_eq_bot_of_perfect_simple _) hg e

/-- All source alternatives but derived G₂(2) have now been discharged.
The remaining group comparison is retained explicitly for final assembly. -/
theorem reduced_of_no_binaryG2_component
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (ρ : Representation (ZMod 2) G V) (hyp : FFHypothesis K ρ)
    {L : Subgroup G} (hL : IsComponent G L) (hr : 1 < primeRank 3 L)
    (d : NoncentralContext K G L) {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hm : ¬ A ≤ centralizer (pCore 3 G : Set G))
    (hg : ¬ Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    Nonempty (ReducedSymmetricModel ρ L A) :=
  reduced_of_component_exclusions earlier ρ hyp hL hr d hA hm
    (not_alternatingEight_component hL d) hg

/-- The full lifted-component comparison in B.5.7, with all intrinsic exclusions
discharged. The only earlier-source parameters are the complete universal B.5.1
and I.1.3 implications. The output retains the original restricted action,
its literal moved central quotient, and the same actor map for both markings. -/
theorem reduced_of_earlier_source
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (multipliers : BinaryG2Exclusion.EarlierMultiplierInput K)
    (ρ : Representation (ZMod 2) G V) (hyp : FFHypothesis K ρ)
    {L : Subgroup G} (hL : IsComponent G L) (hr : 1 < primeRank 3 L)
    (d : NoncentralContext K G L) {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hm : ¬ A ≤ centralizer (pCore 3 G : Set G)) :
    Nonempty (ReducedSymmetricModel ρ L A) :=
  reduced_of_no_binaryG2_component earlier ρ hyp hL hr d hA hm
    (not_binaryG2_component multipliers hL d)

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison
