module
public import Theory.Representation.SL3.DualLiftCentralizers

/-!
# The actual projective line in a doubled dual module

Transvection differences extract every scalar multiple of a coordinate pair
from an additive invariant subgroup. A nonzero first coordinate supplies a
whole graph of a scalar; any vector outside that graph forces the entire
module. Thus the nonzero proper invariant subgroups are exactly the dual
summands indexed by the projective line, without assuming field linearity.

This supplies the odd family used to choose an S-invariant lift in
NonblockMSInvariantLift, at the start of C.1.35's action-normalizer argument.
Source: Aschbacher--Smith, C.1.35, printed p.138.
-/

@[expose] public section
noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Representation.SL3ParabolicNatural
variable {F : Type*} [Field F]

private theorem invariant_coordinate_pair
    (D : AddSubgroup ((Fin 3 → F) × (Fin 3 → F)))
    (hD : ∀ g : SL(3,F), ∀ v ∈ D,
      (specialLinearNatural 3 g v.1, specialLinearNatural 3 g v.2) ∈ D)
    (v : (Fin 3 → F) × (Fin 3 → F)) (hv : v ∈ D) (i j : Fin 3) (a : F) :
    (Pi.single i (a*v.1 j), Pi.single i (a*v.2 j)) ∈ D := by
  have hd {i j : Fin 3} (hij : i ≠ j) (a : F)
      (w : (Fin 3 → F) × (Fin 3 → F)) (hw : w ∈ D) :
      (Pi.single i (a*w.1 j), Pi.single i (a*w.2 j)) ∈ D := by
    have hh := D.sub_mem (hD (transvection hij a) w hw) hw
    change (specialLinearNatural 3 (transvection hij a) w.1-w.1,
      specialLinearNatural 3 (transvection hij a) w.2-w.2) ∈ D at hh
    simpa only [OneCohomology.SLHigherNatural.action_transvection,add_sub_cancel_left] using hh
  by_cases hij : i = j
  · subst j
    obtain ⟨k,hik⟩ : ∃ k : Fin 3, i ≠ k := by fin_cases i <;> decide
    have hh := hd hik a _ (hd hik.symm 1 v hv)
    simpa only [Pi.single_eq_same,one_mul] using hh
  · exact hd hij a v hv

private theorem invariant_diagonal_mem
    (D : AddSubgroup ((Fin 3 → F) × (Fin 3 → F)))
    (hD : ∀ g : SL(3,F), ∀ v ∈ D,
      (specialLinearNatural 3 g v.1, specialLinearNatural 3 g v.2) ∈ D)
    (v : (Fin 3 → F) × (Fin 3 → F)) (hv : v ∈ D) (j : Fin 3) (w : Fin 3 → F) :
    (v.1 j • w, v.2 j • w) ∈ D := by
  have hh := D.sum_mem (fun i (_ : i ∈ Finset.univ) =>
    invariant_coordinate_pair D hD v hv i j (w i))
  have he : (∑ i : Fin 3, (Pi.single i (w i*v.1 j), Pi.single i (w i*v.2 j))) =
      (v.1 j • w, v.2 j • w) := by
    apply Prod.ext <;> funext i <;> simp [Prod.fst_sum,Prod.snd_sum,Finset.sum_apply,mul_comm]
  rwa [he] at hh

/-- Every nonzero proper additive subgroup invariant under the doubled natural
SL₃ action is an entire diagonal copy, even without assumed field linearity. -/
theorem invariant_double_natural_classification
    (D : AddSubgroup ((Fin 3 → F) × (Fin 3 → F))) (hne : D ≠ ⊥) (hlt : D ≠ ⊤)
    (hD : ∀ g : SL(3,F), ∀ v ∈ D,
      (specialLinearNatural 3 g v.1, specialLinearNatural 3 g v.2) ∈ D) :
    (∀ v, v ∈ D ↔ v.1 = 0) ∨ ∃ a : F, ∀ v, v ∈ D ↔ v.2 = a • v.1 := by
  have pure (w : Fin 3 → F) (hw : w ≠ 0) (hm : (0,w) ∈ D) :
      ∀ z : Fin 3 → F, (0,z) ∈ D := by
    obtain ⟨j,hj⟩ := Function.ne_iff.mp hw
    change w j ≠ 0 at hj
    intro z
    have hh := invariant_diagonal_mem D hD (0,w) hm j ((w j)⁻¹ • z)
    simpa only [Pi.zero_apply,zero_smul,smul_inv_smul₀ hj] using hh
  by_cases hz : ∀ v ∈ D, v.1 = 0
  · left
    obtain ⟨x,hx0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hne
    let v := x.val
    have hv : v ∈ D := x.property
    have hv0 : v ≠ 0 := fun hh => hx0 (Subtype.ext hh)
    have hv2 : v.2 ≠ 0 := by
      intro hh
      exact hv0 (Prod.ext (hz v hv) hh)
    have hp := pure v.2 hv2 (by
      convert hv using 1
      exact Prod.ext (hz v hv).symm rfl)
    intro v
    refine ⟨hz v, fun hh => ?_⟩
    convert hp v.2 using 1
    exact Prod.ext hh rfl
  push Not at hz
  obtain ⟨v,hv,hv1⟩ := hz
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hv1
  change v.1 j ≠ 0 at hj
  let a := v.2 j * (v.1 j)⁻¹
  have diag (w : Fin 3 → F) : (w,a • w) ∈ D := by
    have hh := invariant_diagonal_mem D hD v hv j ((v.1 j)⁻¹ • w)
    simpa only [smul_inv_smul₀ hj,smul_smul] using hh
  right
  refine ⟨a,fun w => ⟨?_,?_⟩⟩
  · intro hw
    by_contra hbad
    have hh : (0,w.2-a • w.1) ∈ D := by
      have hh := D.sub_mem hw (diag w.1)
      change (w.1-w.1,w.2-a • w.1) ∈ D at hh
      simpa only [sub_self] using hh
    have hp := pure _ (sub_ne_zero.mpr hbad) hh
    apply hlt
    apply top_unique
    intro z _
    have hh := D.add_mem (diag z.1) (hp (z.2-a • z.1))
    simpa only [Prod.mk_add_mk,add_zero,add_sub_cancel] using hh
  · intro hw
    convert diag w.1 using 1
    exact Prod.ext rfl hw

/-- The same classification on the literal dual modules. -/
theorem invariant_double_dual_classification
    (D : AddSubgroup (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hne : D ≠ ⊥) (hlt : D ≠ ⊤)
    (hD : ∀ g : SL(3,F), ∀ v ∈ D,
      ((specialLinearNatural 3).dual g v.1, (specialLinearNatural 3).dual g v.2) ∈ D) :
    (∀ v, v ∈ D ↔ v.1 = 0) ∨ ∃ a : F, ∀ v, v ∈ D ↔ v.2 = a • v.1 := by
  let e := (dualVectorCoordinates (F := F)).prodCongr dualVectorCoordinates
  let D' := D.map e.toAddEquiv.toAddMonoidHom
  have he (g : SL(3,F)) (v : Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)) :
      e ((specialLinearNatural 3).dual (g.transpose)⁻¹ v.1,
        (specialLinearNatural 3).dual (g.transpose)⁻¹ v.2) =
      (specialLinearNatural 3 g (e v).1,specialLinearNatural 3 g (e v).2) := by
    apply Prod.ext <;> dsimp only [e,LinearEquiv.prodCongr_apply] <;>
      rw [dualVectorCoordinates_action,inv_inv] <;> rfl
  have hmem (v) : e v ∈ D' ↔ v ∈ D := AddSubgroup.mem_map_iff_mem e.injective
  have hne' : D' ≠ ⊥ := by
    intro hh
    apply hne
    exact (AddSubgroup.map_eq_bot_iff_of_injective D e.injective).mp hh
  have hlt' : D' ≠ ⊤ := by
    intro hh
    apply hlt
    apply top_unique
    intro v _
    exact (hmem v).mp (hh ▸ AddSubgroup.mem_top _)
  have hD' : ∀ g : SL(3,F), ∀ v ∈ D',
      (specialLinearNatural 3 g v.1,specialLinearNatural 3 g v.2) ∈ D' := by
    intro g v hv
    obtain ⟨w,hw,rfl⟩ := hv
    change (specialLinearNatural 3 g (e w).1,specialLinearNatural 3 g (e w).2) ∈ D'
    rw [←he]
    exact AddSubgroup.mem_map.mpr ⟨_,hD _ w hw,rfl⟩
  rcases invariant_double_natural_classification D' hne' hlt' hD' with hz | ⟨a,ha⟩
  · left
    intro v
    rw [←hmem, hz]
    exact (dualVectorCoordinates (F := F)).map_eq_zero_iff
  · right
    refine ⟨a,fun v => ?_⟩
    rw [←hmem,ha]
    change dualVectorCoordinates v.2 = a • dualVectorCoordinates v.1 ↔ _
    rw [←map_smul,EmbeddingLike.apply_eq_iff_eq]

end Representation.SL3ParabolicNatural
end

@[expose] public section
noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Representation.SL3ParabolicNatural
variable {F : Type*} [Field F]

/-- The projective line of dual summands, with the second axis at infinity. -/
def dualLine (a : Option F) : Subgroup (Multiplicative
    (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F))) :=
  match a with
  | none => (dualDiagonal 0 1).range
  | some a => (dualDiagonal 1 a).range

theorem mem_dualLine_none (v : Multiplicative
    (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F))) :
    v ∈ dualLine (none : Option F) ↔ v.toAdd.1 = 0 := by
  constructor
  · rintro ⟨f,rfl⟩
    exact zero_smul _ _
  · intro hv
    refine ⟨Multiplicative.ofAdd v.toAdd.2,?_⟩
    apply Multiplicative.toAdd.injective
    change (0 • v.toAdd.2,1 • v.toAdd.2) = v.toAdd
    exact Prod.ext ((zero_smul _ _).trans hv.symm) (one_smul _ _)

theorem mem_dualLine_some (a : F) (v : Multiplicative
    (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F))) :
    v ∈ dualLine (some a) ↔ v.toAdd.2 = a • v.toAdd.1 := by
  constructor
  · rintro ⟨f,rfl⟩
    exact (congrArg (a • ·) (one_smul F f.toAdd)).symm
  · intro hv
    refine ⟨Multiplicative.ofAdd v.toAdd.1,?_⟩
    apply Multiplicative.toAdd.injective
    exact Prod.ext (one_smul _ _) hv.symm

theorem dualLine_injective : Function.Injective (dualLine (F := F)) := by
  let f : Module.Dual F (Fin 3 → F) := LinearMap.proj 0
  have hf : f ≠ 0 := by
    intro h
    have hh := LinearMap.congr_fun h (Pi.single 0 1)
    change (1 : F) = 0 at hh
    exact one_ne_zero hh
  intro a b he
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hm : Multiplicative.ofAdd (f,b • f) ∈ dualLine (some b) :=
        (mem_dualLine_some _ _).mpr rfl
      rw [←he,mem_dualLine_none] at hm
      exact (hf hm).elim
  | some a =>
    have hm : Multiplicative.ofAdd (f,a • f) ∈ dualLine (some a) :=
      (mem_dualLine_some _ _).mpr rfl
    rw [he] at hm
    cases b with
    | none => exact (hf ((mem_dualLine_none _).mp hm)).elim
    | some b =>
      have hh := (mem_dualLine_some _ _).mp hm
      have hab : a = b := smul_left_injective F hf hh
      exact congrArg some hab

/-- There are no additional additive invariant subgroups between zero and
the doubled dual, beyond the actual projective-line family. -/
theorem invariant_dual_subgroup_eq_line
    (D : Subgroup (Multiplicative
      (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F))))
    (hne : D ≠ ⊥) (hlt : D ≠ ⊤)
    (hD : ∀ g : SL(3,F), ∀ v ∈ D,
      Multiplicative.ofAdd
        ((specialLinearNatural 3).dual g v.toAdd.1,
          (specialLinearNatural 3).dual g v.toAdd.2) ∈ D) :
    ∃ a : Option F, D = dualLine a := by
  let E : AddSubgroup (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)) :=
    { carrier := {v | Multiplicative.ofAdd v ∈ D}
      zero_mem' := D.one_mem
      add_mem' := D.mul_mem
      neg_mem' := D.inv_mem }
  have he (v) : v ∈ E ↔ Multiplicative.ofAdd v ∈ D := Iff.rfl
  have hne' : E ≠ ⊥ := by
    intro hh
    apply hne
    ext v
    change v ∈ D ↔ v = 1
    exact (show v.toAdd ∈ E ↔ v.toAdd = 0 by rw [hh]; rfl)
  have hlt' : E ≠ ⊤ := by
    intro hh
    apply hlt
    apply top_unique
    intro v _
    exact (he v.toAdd).mp (hh ▸ AddSubgroup.mem_top _)
  rcases invariant_double_dual_classification E hne' hlt'
    (fun g v hv => hD g (Multiplicative.ofAdd v) hv) with hz | ⟨a,ha⟩
  · refine ⟨none,?_⟩
    ext v
    exact (hz v.toAdd).trans (mem_dualLine_none v).symm
  · refine ⟨some a,?_⟩
    ext v
    exact (ha v.toAdd).trans (mem_dualLine_some a v).symm

end Representation.SL3ParabolicNatural
end
