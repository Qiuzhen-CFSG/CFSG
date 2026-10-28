module

public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import Theory.GroupTheory.PCoreOvergroup

/-!
# The normal-subgroup geometry of a minimal parabolic

This file records the part of B.6.8 which is independent of the later
classification of the odd residual.  The important point is that the maximal
overgroup is retained as an actual subgroup.  Consequently all normal-subgroup
statements below are statements in the ambient group and no quotient
identification is hidden in a coercion.

The two quotient groups used in the source are exposed as `minimalParabolicQuotient`
and `minimalParabolicStarQuotient`.  In particular, `pCore 2` (the literal
`O₂`) is kept separate from the 2-residual, which is deliberately left to the
subsequent structure modules.
-/

namespace CFSG.Quasithin.ChapterB

noncomputable section

variable {H : Type*} [Group H]

/-- The unique maximal subgroup above the Sylow subgroup of a minimal
parabolic.  The definition uses the uniqueness supplied by B.6.1. -/
public def minimalParabolicMax (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) : Subgroup H :=
  Classical.choose (isMinimalParabolicOver_top_iff T |>.mp hP).1

public theorem minimalParabolicMax_spec (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    IsCoatom (minimalParabolicMax T hP) ∧
      (T : Subgroup H) ≤ minimalParabolicMax T hP := by
  exact (Classical.choose_spec (isMinimalParabolicOver_top_iff T |>.mp hP).1).1

public theorem minimalParabolicMax_unique (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) {N : Subgroup H}
    (hN : IsCoatom N) (hTN : (T : Subgroup H) ≤ N) :
    N = minimalParabolicMax T hP := by
  have hu := (Classical.choose_spec (isMinimalParabolicOver_top_iff T |>.mp hP).1).2
  exact hu N ⟨hN, hTN⟩

/-- The normal core of the unique maximal overgroup. -/
public def minimalParabolicCore (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) : Subgroup H :=
    (minimalParabolicMax T hP).normalCore

/-- The ambient two-core, with the notation used in B.6.8. -/
public abbrev minimalParabolicTwoCore : Subgroup H := pCore 2 H

/-- The two quotient `H/O₂(H)` occurring in B.6.8. -/
public abbrev minimalParabolicQuotient : Type _ := H ⧸ minimalParabolicTwoCore (H := H)

/-- The star quotient `H/J` occurring in B.6.8. -/
public abbrev minimalParabolicStarQuotient (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) : Type _ :=
  H ⧸ minimalParabolicCore T hP

private theorem minimalParabolic_hasUniqueMaximal (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    Order.HasUniqueMaximalOver (T : Subgroup H) ⊤ := by
  have hTnormal : ¬ (T : Subgroup H).Normal :=
    (isMinimalParabolicOver_top_iff T |>.mp hP).2
  have hTlt : (T : Subgroup H) < (⊤ : Subgroup H) := by
    refine lt_of_le_of_ne le_top ?_
    intro heq
    apply hTnormal
    rw [heq]
    infer_instance
  refine ⟨?_, ?_⟩
  · exact hTlt
  · refine ⟨minimalParabolicMax T hP, ?_, ?_⟩
    · exact ⟨(minimalParabolicMax_spec T hP).2,
        (minimalParabolicMax_spec T hP).1.covBy_top⟩
    · intro N hN
      exact minimalParabolicMax_unique T hP hN.2.isCoatom hN.1

/-- B.6.8(4): every normal subgroup is either in the core of the maximal
overgroup or, together with the fixed Sylow subgroup, generates `H`. -/
public theorem minimalParabolic_normal_subgroup_dichotomy (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (N : Subgroup H) [Finite H] [N.Normal] :
    N ≤ minimalParabolicCore T hP ∨
      (T : Subgroup H) ⊔ N = ⊤ := by
  exact Subgroup.normal_le_core_or_sup_eq_top_of_uniqueMaximal
    (minimalParabolic_hasUniqueMaximal T hP)
    ⟨(minimalParabolicMax_spec T hP).2, (minimalParabolicMax_spec T hP).1⟩

/-- The two-core is contained in the maximal overgroup core. -/
public theorem minimalParabolicTwoCore_le_core (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    minimalParabolicTwoCore (H := H) ≤ minimalParabolicCore T hP := by
  let Q : Subgroup H := pCore 2 H
  have hQ_T : Q ≤ (T : Subgroup H) :=
    pCore_isPGroup.le_sylow_of_normal T
  have hQ_M : Q ≤ minimalParabolicMax T hP :=
    hQ_T.trans (minimalParabolicMax_spec T hP).2
  exact (Subgroup.normal_le_normalCore.mpr hQ_M)

/-- The intrinsic two-core of the maximal-core is exactly the ambient
two-core.  This is the equality `O₂(J)=O₂(H)` in B.6.8(1). -/
public theorem minimalParabolic_pCore_core_eq (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    (pCore 2 (minimalParabolicCore T hP)).map
        (minimalParabolicCore T hP).subtype = minimalParabolicTwoCore (H := H) := by
  let J := minimalParabolicCore T hP
  let Q := pCore 2 H
  have hJnormal : J.Normal := (minimalParabolicMax T hP).normalCore_normal
  let _ : J.Normal := hJnormal
  have hQJ : Q ≤ J := minimalParabolicTwoCore_le_core T hP
  have hpcJnormal : (pCore 2 J).map J.subtype |>.Normal := by
    exact ConjAct.normal_of_characteristic_of_normal
  have hpcJp : IsPGroup 2 ((pCore 2 J).map J.subtype) :=
    pCore_isPGroup.map J.subtype
  have hle : (pCore 2 J).map J.subtype ≤ Q := by
    exact le_sSup ⟨hpcJnormal, hpcJp⟩
  have hQpJ : Q.subgroupOf J ≤ pCore 2 J := by
    apply le_sSup
    exact ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  have hQmap : (Q.subgroupOf J).map J.subtype = Q :=
    Subgroup.map_subgroupOf_eq_of_le hQJ
  apply le_antisymm
  · exact hle
  · change Q ≤ (pCore 2 J).map J.subtype
    rw [← hQmap]
    exact Subgroup.map_mono hQpJ

/-- A normal subgroup whose image is known to be a two-group is controlled by
the same maximal-overgroup argument.  This is the subgroup form used for the
centralizer kernels in B.6.8(6a--c). -/
public theorem minimalParabolic_normal_kernel_consequence (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (C : Subgroup H) [Finite H] [C.Normal] :
    C ≤ minimalParabolicCore T hP ∨
      (T : Subgroup H) ⊔ C = ⊤ :=
  minimalParabolic_normal_subgroup_dichotomy T hP C

/-- The usual `O²` step in the proof of B.6.8(1).  The argument is stated
for an arbitrary normal residual `K` satisfying the defining factorisation
`H = KT`; it therefore applies verbatim to whichever concrete 2-residual
interface is used by a later module. -/
public theorem minimalParabolic_residual_not_le_core_of_factorization
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal]
    (hKT : (T : Subgroup H) ⊔ K = ⊤) :
    ¬ K ≤ minimalParabolicCore T hP := by
  intro hKJ
  have hTM : (T : Subgroup H) ≤ minimalParabolicMax T hP :=
    (minimalParabolicMax_spec T hP).2
  have hKM : K ≤ minimalParabolicMax T hP :=
    hKJ.trans (Subgroup.normalCore_le _)
  have hsup : (T : Subgroup H) ⊔ K ≤ minimalParabolicMax T hP :=
    sup_le hTM hKM
  rw [hKT] at hsup
  exact (minimalParabolicMax_spec T hP).1.ne_top (top_unique hsup)

end
end CFSG.Quasithin.ChapterB
