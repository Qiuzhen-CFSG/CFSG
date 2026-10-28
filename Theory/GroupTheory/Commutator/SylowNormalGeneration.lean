module

public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.Commutator.NormalizesSupplement

/-!
# Residual commutators from Sylow normal generation

Let Y be a normal p-perfect subgroup supplementing a Sylow subgroup S,
and let A be normalized by S and cover S modulo a normal subgroup R ≤ S.
If S normally generates the whole group, then Y = [Y,A]. Indeed N=[Y,A]
is normal, [Y,S] ≤ NR, and NS is therefore a normal subgroup containing S.
Normal generation gives NS=G; p-perfectness removes the p-group supplement.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
the noncentral Thompson argument in 15.3.11(10), printed p.1124.
-/

public section
namespace Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

/-- Covering the Sylow action modulo a normal subgroup contained in the
Sylow subgroup generates every normal p-perfect supplement by commutators. -/
theorem eq_commutator_of_sylow_normal_generation (S : Sylow p G)
    (Y A R : Subgroup G) [Y.Normal] [R.Normal]
    (hgen : Y ⊔ (S : Subgroup G) = ⊤) (hY : IsPPerfect p Y)
    (hA : (S : Subgroup G) ≤ normalizer (A : Set G))
    (hRS : R ≤ (S : Subgroup G)) (hcover : (S : Subgroup G) ≤ A ⊔ R)
    (hS : normalClosure (S : Set G) = ⊤) : Y = ⁅Y, A⁆ := by
  let N := ⁅Y, A⁆
  let : N.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    refine sup_le (normalizer_commutator_ge_left Y A) ?_
    intro s hs
    rw [mem_normalizer_iff_map_conj_eq]
    change N.map (MulAut.conj s).toMonoidHom = N
    have hy : Y.map (MulAut.conj s).toMonoidHom = Y :=
      mem_normalizer_iff_map_conj_eq.mp (show s ∈ normalizer (Y : Set G) by
        rw [normalizer_eq_top]; trivial)
    have ha : A.map (MulAut.conj s).toMonoidHom = A :=
      mem_normalizer_iff_map_conj_eq.mp (hA hs)
    rw [map_commutator, hy, ha]
  have hcomm : ⁅Y, (S : Subgroup G)⁆ ≤ N ⊔ R := by
    apply commutator_le.mpr
    intro y hy s hs
    obtain ⟨a, ha, r, hr, rfl⟩ := mem_sup_of_normal_right.mp (hcover hs)
    have hyr : ⁅y, r⁆ ∈ R := commutator_le_right (⊤ : Subgroup G) R
      (commutator_mem_commutator (mem_top y) hr)
    have hac : a * ⁅y, r⁆ * a⁻¹ ∈ R := (inferInstance : R.Normal).conj_mem _ hyr a
    rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅y, a⁆ a,
      mul_assoc ⁅y, a⁆ (a * ⁅y, r⁆)]
    exact (N ⊔ R).mul_mem
      ((show N ≤ N ⊔ R from le_sup_left) (commutator_mem_commutator hy ha))
      ((show R ≤ N ⊔ R from le_sup_right) hac)
  let B := (S : Subgroup G) ⊔ N
  have hB : (S : Subgroup G) ⊔ (N ⊔ R) = B := by
    exact le_antisymm (sup_le le_sup_left (sup_le le_sup_right (hRS.trans le_sup_left)))
      (sup_le le_sup_left (le_sup_left.trans le_sup_right))
  let : B.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    refine sup_le ?_ (le_sup_left.trans B.le_normalizer)
    rw [← hB]
    apply le_normalizer_sup_of_commutator_le (S : Subgroup G) Y (S : Subgroup G) (N ⊔ R) le_rfl
    rwa [commutator_comm]
  have htop : B = ⊤ := top_unique (hS.symm.le.trans
    (normalClosure_le_normal (show (S : Subgroup G) ≤ B from le_sup_left)))
  apply le_antisymm _ (commutator_le_left Y A)
  apply le_normal_of_isPPerfect_of_le_sup_pGroup Y N (S : Subgroup G) hY S.isPGroup'
  exact le_top.trans_eq ((sup_comm N (S : Subgroup G)).trans htop).symm

end Subgroup
end
