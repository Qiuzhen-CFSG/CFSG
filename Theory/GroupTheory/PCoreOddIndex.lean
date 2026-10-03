module

public import Theory.PGroupCore

/-!
# Two-subgroups in odd-index overgroups of a two-core

Let `C` contain the two-core `O₂(G)` of a finite group.  If `O₂(G)` has
odd relative index in `C`, then it is the unique Sylow `2`-subgroup of `C`.
Consequently every `2`-subgroup of `G` contained in `C` already lies in
`O₂(G)`.

The proof regards `O₂(G)` inside `C`, uses normality and the odd-index
hypothesis to promote it to a normal Sylow subgroup, and then invokes
uniqueness after extending the given two-subgroup to a Sylow subgroup of
`C`.  This source-neutral calculation is used by the odd-centralizer steps
in Stellmacher's pushing-up argument, Lemmas (1.4) and (2.2).
-/

/-- A `2`-subgroup contained in an odd-index overgroup of `O₂(G)` lies in
`O₂(G)`. -/
public theorem IsPGroup.le_pCore_of_le_oddIndexOverCore
    {G : Type*} [Group G] [Finite G]
    {C A : Subgroup G}
    (hA2 : IsPGroup 2 A)
    (hQC : pCore 2 G ≤ C)
    (hodd : ¬ 2 ∣ ((pCore 2 G).subgroupOf C).index)
    (hAC : A ≤ C) :
    A ≤ pCore 2 G := by
  classical
  let Q : Subgroup G := pCore 2 G
  let QC : Subgroup C := Q.subgroupOf C
  have hQCnormal : QC.Normal :=
    (pCore_normal (p := 2) (G := G)).subgroupOf C
  let _ : QC.Normal := hQCnormal
  have hQCtwo : IsPGroup 2 QC := by
    exact (pCore_isPGroup (p := 2) (G := G)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQC).symm
  let P : Sylow 2 C := hQCtwo.toSylow (by simpa [Q, QC] using hodd)
  have hPnormal : (P : Subgroup C).Normal := by
    change QC.Normal
    infer_instance
  let _ : Unique (Sylow 2 C) := Sylow.unique_of_normal P hPnormal
  let AC : Subgroup C := A.subgroupOf C
  have hACtwo : IsPGroup 2 AC :=
    hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAC).symm
  obtain ⟨U, hACU⟩ := hACtwo.exists_le_sylow
  have hUPC : U = P := Subsingleton.elim U P
  have hACQC : AC ≤ QC := by
    simpa [P, IsPGroup.toSylow_coe, hUPC] using hACU
  intro x hx
  exact hACQC (show (⟨x, hAC hx⟩ : C) ∈ AC from hx)
