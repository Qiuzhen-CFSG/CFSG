module

public import Theory.SpecificGroups.BinaryLinear.TransvectionFiveLocal.KernelStructure
public import Theory.GroupTheory.DihedralCentralProductThree.Marked

/-!
# The marked plus type of the seven-root kernel

Pair each first-row root with the last-column root with the same middle index.
The three dihedral factors commute and have the original transvection as their
common central rotation. They generate the literal kernel, giving its marked
threefold dihedral central-product description.

This is a native SL₅(2) calculation. The comparison with an original ambient
Sylow subgroup in Aschbacher--Smith 12.7.7, printed p.841, remains separate.
-/

namespace BinaryLinear.TransvectionFiveLocal
open Subgroup DihedralGroup DihedralCentralProductSix

private def row (i : Fin 3) : kernel :=
  ⟨root (show (0 : Fin 5) < i.succ.castSucc by simp),
    subset_closure ⟨0,i.succ.castSucc,by simp,Or.inl rfl,rfl⟩⟩

private def column (i : Fin 3) : kernel :=
  ⟨root (show i.succ.castSucc < (4 : Fin 5) from by
    change i.val+1<4
    omega),
    subset_closure ⟨i.succ.castSucc,4,by change i.val+1<4; omega,Or.inr rfl,rfl⟩⟩

private def z : kernel := ⟨transvection,transvection_mem_kernel⟩

private theorem row_square (i : Fin 3) : row i ^ 2 = 1 := by
  apply Subtype.ext
  exact (by decide +kernel : ∀ i : Fin 3, (row i : SL)^2=1) i
private theorem column_square (i : Fin 3) : column i ^ 2 = 1 := by
  apply Subtype.ext
  exact (by decide +kernel : ∀ i : Fin 3, (column i : SL)^2=1) i
private theorem z_square : z^2=1 := by
  apply Subtype.ext
  change transvection^2=1
  simpa only [transvection_orderOf] using pow_orderOf_eq_one transvection

private theorem row_column (i : Fin 3) : row i * column i = column i * row i * z := by
  apply Subtype.ext
  exact (by decide +kernel : ∀ i : Fin 3,
    (row i : SL) * column i = (column i : SL) * row i * transvection) i

private noncomputable def factor (i : Fin 3) : DihedralGroup 4 →* kernel :=
  pairMap (row i) (column i) z (row_square i) (column_square i) z_square (row_column i)

private theorem factor_row (i : Fin 3) : factor i (.sr 0)=row i :=
  pairMap_sr_zero _ _ _ _ _ _ _
private theorem factor_column (i : Fin 3) : factor i (.sr 1)=column i := by
  calc
    factor i (.sr 1)=row i * (row i * column i)^1 :=
      pairMap_sr _ _ _ _ _ _ _ 1
    _=column i := by rw [pow_one,←mul_assoc,←pow_two,row_square,one_mul]
private theorem factor_center (i : Fin 3) : factor i (.r 2)=z :=
  pairMap_r_two _ _ _ _ _ _ _

private theorem factor_commute : Pairwise fun i j =>
    ∀ x y, Commute (factor i x) (factor j y) := by
  intro i j hij x y
  have hrr : Commute (row i) (row j) := by
    apply (commute_iff_eq _ _).mpr
    apply Subtype.ext
    exact (by decide +kernel : ∀ i j : Fin 3, (row i : SL) * row j = (row j : SL) * row i) i j
  have hrc : Commute (row i) (column j) := by
    apply (commute_iff_eq _ _).mpr
    apply Subtype.ext
    exact (by decide +kernel : ∀ i j : Fin 3, i≠j →
      (row i : SL) * column j = (column j : SL) * row i) i j hij
  have hcr : Commute (column i) (row j) := by
    apply (commute_iff_eq _ _).mpr
    apply Subtype.ext
    exact (by decide +kernel : ∀ i j : Fin 3, i≠j →
      (column i : SL) * row j = (row j : SL) * column i) i j hij
  have hcc : Commute (column i) (column j) := by
    apply (commute_iff_eq _ _).mpr
    apply Subtype.ext
    exact (by decide +kernel : ∀ i j : Fin 3,
      (column i : SL) * column j = (column j : SL) * column i) i j
  exact pairMap_commute _ _ _ _ _ _ _ _ _ _ _ _ hrr hrc hcr hcc x y

private theorem factor_generate : (⨆ i, (factor i).range)=⊤ := by
  let A : Subgroup kernel := ⨆ i, (factor i).range
  have hr (i : Fin 3) : row i ∈ A :=
    (le_iSup (fun i => (factor i).range) i) ⟨.sr 0,factor_row i⟩
  have hc (i : Fin 3) : column i ∈ A :=
    (le_iSup (fun i => (factor i).range) i) ⟨.sr 1,factor_column i⟩
  have hz : z ∈ A :=
    (le_iSup (fun i => (factor i).range) 0) ⟨.r 2,factor_center 0⟩
  have hk : kernel ≤ A.map kernel.subtype := by
    apply (closure_le _).mpr
    rintro g ⟨i,j,h,hrj,rfl⟩
    have he : ∀ (i j : Fin 5) (h : i<j), (i=0 ∨ j=4) →
        root h=transvection ∨ ∃ k : Fin 3,
          root h=(row k : SL) ∨ root h=(column k : SL) := by decide +kernel
    rcases he i j h hrj with he | ⟨k,he|he⟩
    · exact he ▸ ⟨z,hz,rfl⟩
    · exact he ▸ ⟨row k,hr k,rfl⟩
    · exact he ▸ ⟨column k,hc k,rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y,hy,he⟩ := hk x.property
  have hxy : y=x := Subtype.ext he
  exact hxy ▸ hy

/-- The literal kernel is the threefold central product of dihedral groups of
order eight, with its row roots, column roots and central involution marked. -/
public theorem kernel_marked_dihedral_three :
    ∃ e : DihedralCentralProductThree.Model ≃* kernel, ∀ i : Fin 3,
      (e (QuotientGroup.mk (Pi.mulSingle i (DihedralGroup.sr 0))) : SL) =
        root (show (0 : Fin 5) < i.succ.castSucc by simp) ∧
      (e (QuotientGroup.mk (Pi.mulSingle i (DihedralGroup.sr 1))) : SL) =
        root (show i.succ.castSucc < (4 : Fin 5) from by
    change i.val+1<4
    omega) ∧
      (e (QuotientGroup.mk (Pi.mulSingle i (DihedralGroup.r 2))) : SL) =
        transvection := by
  have hz (i : Fin 3) : factor i (.r 2)=factor 0 (.r 2) :=
    (factor_center i).trans (factor_center 0).symm
  let e := DihedralCentralProductThree.markedRecognition factor factor_commute hz
    factor_generate kernel_card
  refine ⟨e,fun i => ?_⟩
  change (e (QuotientGroup.mk (Pi.mulSingle i (.sr 0))) : SL)=(row i : SL) ∧
    (e (QuotientGroup.mk (Pi.mulSingle i (.sr 1))) : SL)=(column i : SL) ∧
    (e (QuotientGroup.mk (Pi.mulSingle i (.r 2))) : SL)=(z : SL)
  simp only [e,DihedralCentralProductThree.markedRecognition_single,
    factor_row,factor_column,factor_center,and_self]

end BinaryLinear.TransvectionFiveLocal
