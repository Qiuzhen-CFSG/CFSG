module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups
public import Mathlib.Data.Finset.Sort

/-!
# Positive-rank binary parabolics containing a Sylow subgroup

A proper subgroup of SL(n,2) containing a Sylow two-subgroup stabilizes
some nonempty set of coordinate cuts. If it is not a two-group, these
cuts omit a node of the complete flag. Ordering the cuts gives the
positive-rank flag, with its stabilizer transported through the literal
SL-to-PSL quotient.

This supplies the marked binary row used in Aschbacher--Smith C.2.7(3)(h)
and original 15.2.23, printed pp.145--147 and 1116--1117.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

/-- A proper, non-two-group Sylow overgroup in a binary special linear
group is a parabolic of positive semisimple rank, on the given marking. -/
theorem binaryPositiveRank_of_sylow_overgroup
    {A : Type*} [Group A] [Finite A] {m : ℕ}
    (e : A ≃* SL(m+1,ZMod 2)) (P : Subgroup A)
    (Q : Sylow 2 A) (hQP : (Q : Subgroup A) ≤ P)
    (hproper : P ≠ ⊤) (hnot : ¬ IsPGroup 2 P) :
    IsBinaryPositiveRankParabolic P (m+1) := by
  classical
  let a := e.trans (BinaryLinear.OuterCyclic.slEquivLinear (m+1))
  let S := Q.mapSurjective (f := a.toMonoidHom) a.surjective
  obtain ⟨b,cuts,hS,hP⟩ := BinaryLinear.SylowFlagOvergroups.exists_flag_of_sylow_le
    S (P.map a.toMonoidHom) (map_mono hQP)
  let c := cuts.toFinset
  have hc : c ≠ Finset.univ := by
    intro hh
    have he : cuts = Set.univ := by simpa only [c, Set.toFinset_eq_univ] using hh
    have hp : IsPGroup 2 (P.map a.toMonoidHom) := by rw [hP,he,←hS]; exact S.isPGroup'
    exact hnot (hp.of_equiv (a.subgroupMap P).symm)
  have hcard : c.card < m := by
    have ht := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ c,hc⟩)
    simpa using ht
  have hpos : 0 < c.card := by
    by_contra hh
    have hc0 : c = ∅ := Finset.card_eq_zero.mp (by omega)
    have he : cuts = ∅ := by simpa only [c,Set.toFinset_eq_empty] using hc0
    apply hproper
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_top_of_surjective _ a.surjective,hP,he]
    simp [BinaryLinear.InvariantNodeActions.cutStabilizer]
  let w := c.orderEmbOfFin rfl
  let f : LinearFlag (ZMod 2) (m+1) c.card := {
    space := fun i => BinaryLinear.InvariantNodeActions.cutSpace b (w i)
    nonzero := fun i => BinaryLinear.InvariantNodeActions.cutSpace_ne_bot b (w i)
    proper := fun i => BinaryLinear.InvariantNodeActions.cutSpace_ne_top b (w i)
    increasing := by
      intro i j hij
      have hw := w.strictMono hij
      apply lt_of_le_of_ne (BinaryLinear.InvariantNodeActions.cutSpace_mono b hw.le)
      intro he
      have hd := congrArg (fun U : Submodule (ZMod 2) (BinaryLinear.OuterCyclic.Space (m+1)) => Module.finrank (ZMod 2) U) he
      simp only [BinaryLinear.InvariantNodeActions.cutSpace_finrank] at hd
      have hh : (w i).val < (w j).val := hw
      omega }
  have hf : P.map e.toMonoidHom = f.stabilizer := by
    apply map_injective (f := (BinaryLinear.OuterCyclic.slEquivLinear (m+1)).toMonoidHom)
      (BinaryLinear.OuterCyclic.slEquivLinear (m+1)).injective
    rw [map_map]
    change P.map a.toMonoidHom = _
    rw [hP]
    ext g
    rw [mem_map_equiv,BinaryLinear.InvariantNodeActions.mem_cutStabilizer]
    change (∀ j ∈ cuts, ∀ v, g v ∈ BinaryLinear.InvariantNodeActions.cutSpace b j ↔
        v ∈ BinaryLinear.InvariantNodeActions.cutSpace b j) ↔
      (BinaryLinear.OuterCyclic.slEquivLinear (m+1)).symm g ∈ ⨅ i, linearStabilizer (f.space i)
    simp only [mem_iInf]
    have he (i : Fin c.card) :
        (BinaryLinear.OuterCyclic.slEquivLinear (m+1)).symm g ∈ linearStabilizer (f.space i) ↔
        ∀ v, g v ∈ f.space i ↔ v ∈ f.space i := by
      rw [linearStabilizer,mem_comap,Submodule.stabilizer_coe,MulAction.mem_stabilizer_set]
      change (∀ v, (BinaryLinear.OuterCyclic.slEquivLinear (m+1))
        ((BinaryLinear.OuterCyclic.slEquivLinear (m+1)).symm g) v ∈ f.space i ↔ v ∈ f.space i) ↔ _
      rw [MulEquiv.apply_symm_apply]
    simp_rw [he]
    constructor
    · intro hg i
      exact hg (w i) (by simpa only [c,Set.mem_toFinset] using c.orderEmbOfFin_mem rfl i)
    · intro hg j hj
      let i := (c.orderIsoOfFin rfl).symm ⟨j,by simpa only [c,Set.mem_toFinset] using hj⟩
      have hi : w i = j := congrArg Subtype.val ((c.orderIsoOfFin rfl).apply_symm_apply
        ⟨j,by simpa only [c,Set.mem_toFinset] using hj⟩)
      simpa only [f,hi] using hg i
  let q := QuotientGroup.mk' (center SL(m+1,ZMod 2))
  let eqp := (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < m+1)).symm
  refine ⟨e.trans eqp,c.card,hpos,by omega,f,?_⟩
  change P.map (q.comp e.toMonoidHom) = f.stabilizer.map q
  rw [←map_map,hf]


end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
