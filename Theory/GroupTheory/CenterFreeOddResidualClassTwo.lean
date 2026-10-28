module
public import Theory.GroupTheory.OddIndexCoreCentralizes

/-!
# A central residual action forces a class-two core

Let normal E supplement a supplied Sylow two-subgroup in a finite
center-free group P. Let normal Q be a two-group such that E has odd
image in P/Q. If normal Z centralizes Q and [E∩Q,Q]≤Z, then [Q,Q]≤Z.
Neither abelianness of Q/Z nor a quotient-cardinality bound is assumed.

Put R=E∩Q and D=[Q,Q]. The three-subgroups lemma gives [D,R]=1 and,
after passage modulo Z, [D,E]≤Z. Center-freeness and the Sylow supplement
make C_D(E) trivial. The normal two-subgroup R has odd index in E and
centralizes D. The existing odd-index core-centralizer splitting theorem
therefore identifies D with its commutator with E, which lies in Z.

This source-neutral lemma supplies Qmiddle/Zmiddle abelianity in the
small branch of Stellmacher (10.1)(a3), printed p.61/PDF p.51,
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Subgroup

public theorem commutator_le_of_centerfree_odd_residual_central_layer
    {P : Type*} [Group P] [Finite P]
    (S : Sylow 2 P) (E Q Z : Subgroup P) [E.Normal] [Q.Normal] [Z.Normal]
    (hcover : E ⊔ (S : Subgroup P) = ⊤) (hQ : IsPGroup 2 Q)
    (hcenter : center P = ⊥)
    (hodd : Odd (Nat.card (E.map (QuotientGroup.mk' Q))))
    (hZcentral : Z ≤ centralizer (Q : Set P))
    (hRQ : ⁅E ⊓ Q, Q⁆ ≤ Z) : ⁅Q,Q⁆ ≤ Z := by
  let R := E ⊓ Q
  let D := ⁅Q,Q⁆
  have hDQ : D ≤ Q := commutator_le_left Q Q
  have hDp : IsPGroup 2 D := hQ.to_le hDQ
  have hRQQ : ⁅⁅R,Q⁆,Q⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hRQ.trans hZcentral)
  have hDR : ⁅D,R⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate
      (by rwa [commutator_comm Q R]) hRQQ
  have hRE : R ≤ E := inf_le_left
  have hRp : IsPGroup 2 R := hQ.to_le inf_le_right
  have hRodd : Odd (R.subgroupOf E).index := by
    change Odd (R.relIndex E)
    dsimp [R]
    rw [inf_relIndex_left]
    rw [← QuotientGroup.ker_mk' Q, relIndex_ker]
    exact hodd
  have hDfixed : D ⊓ centralizer (E : Set P) = ⊥ :=
    inf_centralizer_eq_bot_of_centerfree_sylow_supplement S E D hcover hDp hcenter
  have hDE : ⁅D,E⁆ ≤ Z := by
    let π := QuotientGroup.mk' Z
    let Qbar := Q.map π
    let Ebar := E.map π
    have hEQ : ⁅E,Q⁆ ≤ R := commutator_le_inf E Q
    have hEQQ : ⁅⁅Ebar,Qbar⁆,Qbar⁆ = ⊥ := by
      rw [← map_commutator, ← map_commutator]
      apply (map_eq_bot_iff _).mpr
      rw [QuotientGroup.ker_mk']
      exact (commutator_mono hEQ le_rfl).trans hRQ
    have hQQE : ⁅⁅Qbar,Qbar⁆,Ebar⁆ = ⊥ :=
      commutator_commutator_eq_bot_of_rotate
        (by rwa [commutator_comm Qbar Ebar]) hEQQ
    have hh : (⁅D,E⁆).map π = ⊥ := by
      rw [map_commutator]
      change ⁅(⁅Q,Q⁆).map π,Ebar⁆ = ⊥
      rw [map_commutator]
      exact hQQE
    simpa only [π,QuotientGroup.ker_mk'] using (map_eq_bot_iff _).mp hh
  let _ : Group.IsNilpotent D := hDp.isNilpotent
  exact le_of_odd_index_core_centralizes E R D Z hRE hRp hRodd hDp
    inferInstance le_normalizer_of_normal
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hDR)) hDfixed hDE

end Subgroup
