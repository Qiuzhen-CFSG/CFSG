module

public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal.Quotient

/-!
# Residual intersection with the unique Sylow maximal subgroup

In a finite solvable group, the unique maximal subgroup containing a given
Sylow 2-subgroup meets the 2-residual inside its normal core. Modulo the
normal core, the primitive local structure gives an odd normal complement
to the Sylow image. This complement is the quotient's 2-residual and meets
the maximal-subgroup image trivially; residual functoriality proves the claim.

This is the residual intersection underlying Stellmacher (3.3), Journal of
Algebra 190 (1997), pp. 21--22. It supplies the maximal-subgroup exclusion
needed for the generation assertion in (7.8). No core-free hypothesis is
required for this inclusion.
-/

namespace Stellmacher.SectionThree

/-- The residual meets the unique Sylow maximal only in its normal core. -/
public theorem residual_inf_unique_maximal_le_normalCore
    {Q : Type*} [Group Q] [Finite Q]
    (T B : Subgroup Q) (Tₛ : Sylow 2 Q)
    (hT : (Tₛ : Subgroup Q) = T)
    (hB : IsCoatom B) (hTB : T ≤ B)
    (huniq : ∀ M : Subgroup Q, IsCoatom M → T ≤ M → M = B)
    (hsolv : Group.IsSolvable Q) :
    twoResidualAmbient (⊤ : Subgroup Q) ⊓ B ≤ B.normalCore := by
  classical
  obtain ⟨p, K, hp, hpodd, hKn, hKe, hKB, hKT, _⟩ :=
    quotientCoreFree_data T B Tₛ hT hB hTB huniq hsolv
  let N := B.normalCore
  let q : Q →* Q ⧸ N := QuotientGroup.mk' N
  let Tbar : Sylow 2 (Q ⧸ N) := Tₛ.mapSurjective (QuotientGroup.mk'_surjective N)
  have hTbar : (Tbar : Subgroup (Q ⧸ N)) = T.map q := by
    change (Tₛ : Subgroup Q).map q = T.map q
    rw [hT]
  have hp2 : p ≠ 2 := by
    intro hp2
    subst p
    obtain ⟨n, hn⟩ := hpodd
    omega
  have hKp : IsPGroup p K := by
    let _ := hKe
    exact IsElementaryAbelian.isPGroup p K
  have hRbar : twoResidualAmbient (⊤ : Subgroup (Q ⧸ N)) = K :=
    twoResidualAmbient_top_eq_of_normal_complement_sylow_two
      hp hp2 K (T.map q) Tbar hTbar hKn hKp hKT
  have hRmap : (twoResidualAmbient (⊤ : Subgroup Q)).map q = K := by
    rw [twoResidualAmbient_top_eq_hktPResidual, map_hktPResidual_quotient,
      ← twoResidualAmbient_top_eq_hktPResidual, hRbar]
  intro x hx
  have hxK : q x ∈ K := by
    rw [← hRmap]
    exact Subgroup.mem_map_of_mem q hx.1
  have hxB : q x ∈ B.map q := Subgroup.mem_map_of_mem q hx.2
  have hxbot : q x ∈ (⊥ : Subgroup (Q ⧸ N)) := by
    rw [← hKB]
    exact ⟨hxK, hxB⟩
  exact (QuotientGroup.eq_one_iff (N := N) x).mp hxbot

end Stellmacher.SectionThree

