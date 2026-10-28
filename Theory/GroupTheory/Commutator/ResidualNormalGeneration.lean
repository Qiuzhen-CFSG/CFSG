module
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# Residual generation by a normally generating prime-group actor

Let K be a normal p-perfect supplement to T. If T normalizes a p-group R
whose normal closure contains K, then K=[K,R]. The commutator C is normal,
and RC is normal and contains R, hence contains K. P-perfectness removes
the p-group supplement R.
Source: Aschbacher–Smith, D.1.4, printed p.176, equation (!).
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
theorem eq_commutator_of_normalClosure_contains
    (K T R : Subgroup G) [K.Normal] (hgen : K ⊔ T = ⊤)
    (hK : IsPPerfect p K) (hR : IsPGroup p R)
    (hTR : T ≤ normalizer (R : Set G))
    (hKN : K ≤ normalClosure (R : Set G)) : K = ⁅K,R⁆ := by
  let C := ⁅K,R⁆
  let : C.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    refine sup_le (normalizer_commutator_ge_left K R) ?_
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change C.map (MulAut.conj t).toMonoidHom = C
    have hk : K.map (MulAut.conj t).toMonoidHom = K :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top t))
    have hr : R.map (MulAut.conj t).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp (hTR ht)
    rw [map_commutator,hk,hr]
  let D := R ⊔ C
  let : D.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    refine sup_le ?_ ?_
    · exact le_normalizer_sup_of_commutator_le R K R C le_rfl (commutator_comm R K).le
    · exact (le_inf hTR le_normalizer_of_normal).trans
        (normalizer_inf_normalizer_le_normalizer_sup R C)
  have hKD : K ≤ D := hKN.trans (normalClosure_le_normal (show R ≤ D from le_sup_left))
  exact le_antisymm
    (le_normal_of_isPPerfect_of_le_sup_pGroup K C R hK hR
      (hKD.trans_eq (sup_comm R C)))
    (commutator_le_left K R)
end Subgroup

