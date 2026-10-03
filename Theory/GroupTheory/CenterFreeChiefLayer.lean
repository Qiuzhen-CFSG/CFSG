module
public import Theory.GroupTheory.CenterFreeOddImageCore

/-!
# Abelianity and central commutators of a chief preimage

In a finite center-free group P, let normal E supplement a Sylow
two-subgroup. A normal two-subgroup C inside Q is abelian whenever
[C,E] lies in a normal subgroup Z centralizing Q. If Q=[Q,E]C, then
[C,Q] lies in Z as well. No action irreducibility is assumed here.

The three-subgroups lemma puts [C,C] in C_C(E). The center-free normal
two-subgroup centralizer theorem kills this subgroup, proving C abelian.
Modulo Z, the same three-subgroups calculation makes C centralize
[Q,E]; generation of Q by that subgroup and C gives the second bound.

These are the elementary commutator reductions for the nonisomorphic
chief-module transfer in Stellmacher (9.1), Journal of Algebra190 (1997),
p.48. The later comparison of modules and complement argument are
separate obligations.
-/

namespace Subgroup
public theorem centerfree_chief_layer_commutators
    {P : Type*} [Group P] [Finite P]
    (S : Sylow 2 P) (E Q C Z : Subgroup P)
    [E.Normal] [C.Normal] [Z.Normal]
    (hcover : E ⊔ (S : Subgroup P) = ⊤)
    (hCp : IsPGroup 2 C) (hcenter : center P = ⊥)
    (hCQ : C ≤ Q) (hZcentral : Z ≤ centralizer (Q : Set P))
    (hCE : ⁅C, E⁆ ≤ Z) (hQgen : ⁅Q, E⁆ ⊔ C = Q) :
    IsMulCommutative C ∧ ⁅C, Q⁆ ≤ Z := by
  have hCfixed : C ⊓ centralizer (E : Set P) = ⊥ :=
    inf_centralizer_eq_bot_of_centerfree_sylow_supplement S E C hcover hCp hcenter
  have hCEC : ⁅⁅C, E⁆, C⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (hCE.trans (hZcentral.trans (centralizer_le hCQ)))
  have hCCE : ⁅⁅C, C⁆, E⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate hCEC (by rwa [commutator_comm E C])
  have hCC : ⁅C, C⁆ = ⊥ := by
    apply bot_unique
    rw [← hCfixed]
    exact le_inf (commutator_le_left C C)
      (commutator_eq_bot_iff_le_centralizer.mp hCCE)
  refine ⟨commutator_self_eq_bot_iff.mp hCC, ?_⟩
  let f := QuotientGroup.mk' Z
  have hfker : f.ker = Z := QuotientGroup.ker_mk' Z
  let Cbar := C.map f
  let Ebar := E.map f
  let Qbar := Q.map f
  have hCEbar : ⁅Cbar, Ebar⁆ = ⊥ := by
    rw [← map_commutator]
    exact (map_eq_bot_iff _).mpr (by simpa only [hfker] using hCE)
  have hCQbar : ⁅Qbar, Cbar⁆ ≤ Cbar := by
    rw [← map_commutator]
    exact map_mono (commutator_le_right Q C)
  have hrotate : ⁅⁅Qbar, Cbar⁆, Ebar⁆ = ⊥ :=
    bot_unique ((commutator_mono hCQbar le_rfl).trans hCEbar.le)
  have hEQC : ⁅⁅Ebar, Qbar⁆, Cbar⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate hrotate (by rw [hCEbar, commutator_bot_left])
  have hQbar : ⁅Qbar, Ebar⁆ ⊔ Cbar = Qbar := by
    rw [← map_commutator, ← map_sup, hQgen]
  have hCCbar : ⁅Cbar, Cbar⁆ = ⊥ := by rw [← map_commutator, hCC, map_bot]
  have hCQQ : ⁅Cbar, Qbar⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    rw [← hQbar]
    apply sup_le
    · apply commutator_eq_bot_iff_le_centralizer.mp
      rwa [commutator_comm Qbar Ebar]
    · exact commutator_eq_bot_iff_le_centralizer.mp hCCbar
  have hmap : (⁅C, Q⁆).map f = ⊥ := by rw [map_commutator]; exact hCQQ
  simpa only [hfker] using (map_eq_bot_iff _).mp hmap
end Subgroup
