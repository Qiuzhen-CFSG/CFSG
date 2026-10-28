module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Actions
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.Elementary
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# The residual-normalizer step in component generation

The equality `O²(Y₀O₂(L)) = Y₀` in 15.3.49(i) needs justification.
Relative subnormality puts `O₂(L)` in `O₂(H) ≤ M = N_G(Y₀)`.
Consequently `Y₀` is normal in `Y₀O₂(L)`, and its two-perfectness identifies
it with that product's two-residual. If `[L,Y₀] ≤ O₂(L)`, then `L` normalizes
the product and its characteristic residual, so `L ≤ M`.

The identity `θ(M ∩ H) = Y₀` now contradicts a factor whose order-three
generators escape `Y₀`. The remaining B.5.6 analysis must establish both
this escape and the commutator containment; they are explicit inputs here.
`IsPPerfect 2 Y₀` follows from the source definition `Y₀ = O²(C_Y(V))`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(i), printed pp.1143–1144.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

private theorem normalizes_residual_of_commutator_le
    (Y0 Q L : Subgroup G) (hY : IsPPerfect 2 Y0) (hQ : IsPGroup 2 Q)
    (hQY : Q ≤ normalizer (Y0 : Set G)) (hLQ : L ≤ normalizer (Q : Set G))
    (hcomm : ⁅L, Y0⁆ ≤ Q) : L ≤ normalizer (Y0 : Set G) := by
  have hres := embedded_pResidual_join_pGroup Y0 Q hY hQ hQY
  have hprod : L ≤ normalizer (Y0 ⊔ Q : Subgroup G) := by
    apply le_normalizer_iff.mpr
    intro l hl y hy
    have hmap : (Y0 ⊔ Q).map (MulAut.conj l).toMonoidHom ≤ Y0 ⊔ Q := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro x ⟨a, ha, rfl⟩
        change MulAut.conj l a ∈ Y0 ⊔ Q
        rw [conj_eq_commutatorElement_mul]
        exact mul_mem (mem_sup_right (hcomm (commutator_mem_commutator hl ha)))
          (mem_sup_left ha)
      · have he : Q.map (MulAut.conj l).toMonoidHom = Q :=
          mem_normalizer_iff_map_conj_eq.mp (hLQ hl)
        rw [he]
        exact le_sup_right
    exact hmap (mem_map_of_mem _ hy)
  rw [← hres]
  exact hprod.trans (normalizer_le_normalizer_characteristic_image
    (Y0 ⊔ Q) (pResidual 2 ↥(Y0 ⊔ Q)))

/-- A relatively subnormal subgroup acting trivially on `Y₀` modulo its
two-core normalizes `Y₀`, hence lies in its actual normalizer `M`. -/
theorem le_M_of_commutator_le_twoCore [Finite G]
    (H M Y0 L : Subgroup G) (hY : IsPPerfect 2 Y0)
    (hN : normalizer (Y0 : Set G) = M)
    (hLH : L ≤ H) (hsub : (L.subgroupOf H).IsSubnormal)
    (hQM : localTwoCore H ≤ M) (hcomm : ⁅L, Y0⁆ ≤ localTwoCore L) : L ≤ M := by
  have hQL : L ≤ normalizer (localTwoCore L : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hQY : localTwoCore L ≤ normalizer (Y0 : Set G) := by
    rw [hN]
    exact (pCoreAmbient_mono_of_isSubnormalIn L H 2 hLH hsub).trans hQM
  rw [← hN]
  exact normalizes_residual_of_commutator_le Y0 (localTwoCore L) L hY
    (pCore_isPGroup.map L.subtype) hQY hQL hcomm

/-- The contradiction used to remove the solvable B.5.6 factors: their
order-three generators cannot escape `Y₀` and centralize it modulo the
two-core. The factor and module analysis must supply the escape premise. -/
theorem commutator_not_le_twoCore_of_theta [Finite G]
    (H M Y0 L : Subgroup G) (hY : IsPPerfect 2 Y0)
    (hN : normalizer (Y0 : Set G) = M)
    (hLH : L ≤ H) (hsub : (L.subgroupOf H).IsSubnormal)
    (hQM : localTwoCore H ≤ M) (hθ : theta (M ⊓ H) = Y0)
    (hthree : ¬ theta L ≤ Y0) : ¬ ⁅L, Y0⁆ ≤ localTwoCore L := by
  intro hcomm
  have hLM := le_M_of_commutator_le_twoCore H M Y0 L hY hN hLH hsub hQM hcomm
  exact hthree ((theta_mono (le_inf hLM hLH)).trans_eq hθ)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
