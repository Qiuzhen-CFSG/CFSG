module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups
public import Mathlib.Data.Finset.Sort

/-!
# Proper binary parabolics containing a Sylow subgroup

Every proper Sylow overgroup in SL(n,2) is the stabilizer of a nonempty
proper partial flag under the supplied matrix marking. The complete flag
is permitted, as required by the parabolic assertions in 15.1.20(2c).
This extends the positive-semisimple-rank interface in BinaryFlags without
imposing a non-two-group hypothesis on the marked subgroup.

Source: Aschbacher--Smith 15.1.20(2c) and 15.1.22(3), pp.1095 and
1098--1100. The proof uses the checked binary Sylow-overgroup theorem.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

/-- Every proper binary Sylow overgroup is a nonempty flag stabilizer,
with the literal supplied isomorphism, including the full-flag case. -/
theorem binary_flag_of_sylow_overgroup
    {A : Type*} [Group A] [Finite A] {m : ℕ}
    (e : A ≃* SL(m+1,ZMod 2)) (P : Subgroup A)
    (Q : Sylow 2 A) (hQP : (Q : Subgroup A) ≤ P)
    (hproper : P ≠ ⊤) :
    ∃ k : ℕ, 0 < k ∧ ∃ f : LinearFlag (ZMod 2) (m+1) k,
      P.map e.toMonoidHom = f.stabilizer := by
  classical
  let a := e.trans (BinaryLinear.OuterCyclic.slEquivLinear (m+1))
  let S := Q.mapSurjective (f := a.toMonoidHom) a.surjective
  obtain ⟨b,cuts,hS,hP⟩ := BinaryLinear.SylowFlagOvergroups.exists_flag_of_sylow_le
    S (P.map a.toMonoidHom) (map_mono hQP)
  let c := cuts.toFinset
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
  exact ⟨c.card,hpos,f,hf⟩

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
