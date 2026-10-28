module
public import Theory.SpecificGroups.SymplecticFour.PointPairGeneration
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.LargeMovement

/-!
# Individual generation at the marked point

An unequal mover in the standard Sylow fixes precisely the standard point.
Conjugating it to a different point prevents it from lying in the original
point parabolic: a two-group in that parabolic fixes its point vector.
Any subgroup containing the whole point local and this mover is therefore
all of Sp₄. The proof retains the actual conjugator and coefficient field.

The consumer is CriticalReduction.ContainedIndividualGeneration, the
noncentral-intersection alternative of MS93 (5.5)(c), printed pp.915--917.
-/

public noncomputable section
open Subgroup Matrix Representation
namespace Theory.SpecificGroups.SymplecticFour.PointIndividualGeneration
open CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem pgroup_le_local {n : ℕ} (hcard : Nat.card F=2^n) (hn : 1<n)
    (T : Subgroup (Sp F)) (hTP : T ≤ pointParabolic) (hT : IsPGroup 2 T) :
    T ≤ pointLocal := by
  let S : Sylow 2 (pointParabolic (F := F)) := (unipotentSylow hcard (by omega)).subtype
    (unipotent_le_borel.trans inf_le_left)
  have hSN : (S : Subgroup (pointParabolic (F := F))) ≤ pointLocal.subgroupOf pointParabolic :=
    comap_mono (show unipotent ≤ pointLocal (F := F) from inf_le_left)
  have hle := hT.comap_subtype.le_normalClosure_sylow S
  have hle' : T.subgroupOf pointParabolic ≤ pointLocal.subgroupOf pointParabolic :=
    hle.trans (normalClosure_le_normal hSN)
  intro x hx
  exact hle' (show (⟨x,hTP hx⟩ : pointParabolic) ∈ T.subgroupOf pointParabolic from hx)

omit [CharP F 2] in
/-- A mover with its unique fixed point moved cannot remain in the point parabolic. -/
theorem conjugate_mover_not_point {n : ℕ} (hcard : Nat.card F=2^n) (hn : 1<n)
    (E : Subgroup (unipotent (F := F))) (hfixed : fixed E = point F)
    (w : Sp F) (hw : w ∉ pointParabolic) :
    ¬ (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom ≤ pointParabolic := by
  intro hp
  have hE2 := ((unipotentSylow hcard (by omega)).isPGroup'.to_le
    (map_subtype_le E)).map (MulAut.conj w).toMonoidHom
  have hl := pgroup_le_local hcard hn _ hp hE2
  have hv : w⁻¹ • e (F := F) 0 ∈ fixed E := by
    rw [fixed,mem_invariants]
    intro y
    have he := (mem_pointLocal_iff_fixed _).mp (hl (mem_map_of_mem
      (MulAut.conj w).toMonoidHom (mem_map_of_mem unipotent.subtype y.property)))
    change (w*y.val.val*w⁻¹) • e (F := F) 0 = e 0 at he
    change y.val.val • (w⁻¹ • e (F := F) 0) = w⁻¹ • e 0
    have hh := congrArg (fun z => w⁻¹ • z) he
    simpa only [mul_smul,inv_smul_smul] using hh
  rw [hfixed] at hv
  have hinv : w⁻¹ ∈ pointParabolic := by
    rw [mem_pointParabolic_iff]
    simpa [mem_point_iff,smul_eq_mulVec,e,Matrix.mulVec_single] using hv
  exact hw (by simpa only [inv_inv] using pointParabolic.inv_mem hinv)

/-- The whole point local and a mover fixing a different point generate Sp₄. -/
theorem generate_of_pointLocal_le {n : ℕ} (hcard : Nat.card F=2^n) (hn : 1<n)
    (A : Subgroup (Sp F)) (E : Subgroup (unipotent (F := F)))
    (hfixed : fixed E = point F) (w : Sp F) (hw : w ∉ pointParabolic)
    (hL : pointLocal ≤ A ⊔ (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom) :
    A ⊔ (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom = ⊤ := by
  by_contra htop
  exact conjugate_mover_not_point hcard hn E hfixed w hw
    (le_sup_right.trans (PointPairGeneration.overgroup_pointLocal _ hL htop))

end Theory.SpecificGroups.SymplecticFour.PointIndividualGeneration
