module
public import Theory.GroupTheory.CommutingFactorIntersection
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Commutators on two invariant direct factors

If an actor preserves two commuting disjoint factors, its commutator splits
along them. When the total commutator lies in the first factor times a
subgroup Z of the second and contains Z, its displacement on the second
factor is exactly Z.

For two such splittings with distinct disjoint point subgroups, the two
second factors commute. Each point then lies in the opposite first factor,
with an exact cross-commutator identity. This retains both factors; no
triviality of either original action is inferred.

Source application: Aschbacher–Smith, 14.7.6, printed pp.1044–1045,
the critical-pair calculation in refs/quasithin.pdf.
-/

public section
open scoped Pointwise IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

/-- Displacements distribute over two commuting factors preserved by the actor. -/
theorem commutator_sup_of_commuting_factors
    (W C B : Subgroup G) (hc : W ≤ centralizer (C : Set G))
    (hnC : B ≤ normalizer (C : Set G)) :
    ⁅W ⊔ C,B⁆ = ⁅W,B⁆ ⊔ ⁅C,B⁆ := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro u hu b hb
    have hu' : u ∈ (W : Set G) * (C : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left W C
        ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))]
      exact hu
    obtain ⟨w,hw,c,hc',rfl⟩ := hu'
    have hcb : ⁅c,b⁆ ∈ C :=
      le_normalizer_iff_commutator_le_left.mp hnC (commutator_mem_commutator hc' hb)
    have he : w * ⁅c,b⁆ = ⁅c,b⁆ * w := (hc hw _ hcb).symm
    rw [commutatorElement_mul_left_eq_conj_mul,he,mul_inv_cancel_right]
    exact (⁅W,B⁆ ⊔ ⁅C,B⁆).mul_mem
      (mem_sup_right (commutator_mem_commutator hc' hb))
      (mem_sup_left (commutator_mem_commutator hw hb))
  · exact sup_le (commutator_mono le_sup_left le_rfl)
      (commutator_mono le_sup_right le_rfl)

/-- The displacement on the second factor is the full specified point subgroup. -/
theorem split_commutator_point
    (U W C Z B : Subgroup G)
    (hc : W ≤ centralizer (C : Set G)) (hd : Disjoint W C)
    (hs : W ⊔ C = U) (hz : Z ≤ C)
    (hnW : B ≤ normalizer (W : Set G)) (hnC : B ≤ normalizer (C : Set G))
    (hA : ⁅U,B⁆ ≤ W ⊔ Z) (hZ : Z ≤ ⁅U,B⁆) :
    ⁅U,B⁆ ⊓ C = Z ∧ ⁅C,B⁆ = Z ∧ ⁅W,B⁆ = ⁅U,B⁆ ⊓ W ∧
      (⁅U,B⁆ ⊓ W) ⊔ Z = ⁅U,B⁆ ∧ Disjoint (⁅U,B⁆ ⊓ W) Z := by
  have hWC : (W ⊔ Z) ⊓ C = Z := by
    have hh := sup_inf_sup_eq_of_disjoint_commuting_factors W C W Z ⊥ C
      hd hc le_rfl hz bot_le le_rfl
    simpa only [bot_sup_eq,inf_bot_eq,bot_sup_eq,inf_eq_left.mpr hz] using hh
  have hAC : ⁅U,B⁆ ⊓ C = Z :=
    le_antisymm ((inf_le_inf_right C hA).trans hWC.le) (le_inf hZ hz)
  have hWB : ⁅W,B⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hnW
  have hCB : ⁅C,B⁆ ≤ C := le_normalizer_iff_commutator_le_left.mp hnC
  have hsplit : ⁅U,B⁆ = ⁅W,B⁆ ⊔ ⁅C,B⁆ := by
    rw [←hs,commutator_sup_of_commuting_factors W C B hc hnC]
  have hCBZ : ⁅C,B⁆ = Z := by
    have hh := sup_inf_sup_eq_of_disjoint_commuting_factors W C
      ⁅W,B⁆ ⁅C,B⁆ ⊥ C hd hc hWB hCB bot_le le_rfl
    simpa only [←hsplit,bot_sup_eq,inf_bot_eq,bot_sup_eq,inf_eq_left.mpr hCB,hAC] using hh.symm
  have hAW : ⁅U,B⁆ ⊓ W = ⁅W,B⁆ := by
    have hh := sup_inf_sup_eq_of_disjoint_commuting_factors W C
      ⁅W,B⁆ ⁅C,B⁆ W ⊥ hd hc hWB hCB le_rfl bot_le
    simpa only [←hsplit,sup_bot_eq,inf_bot_eq,sup_bot_eq,inf_eq_left.mpr hWB] using hh
  exact ⟨hAC,hCBZ,hAW.symm,by rw [hAW,←hCBZ,←hsplit],
    hd.mono inf_le_right hz⟩

/-- Two reciprocal splittings force commuting second factors and put each
point in the opposite first factor, with exact cross-commutators. -/
theorem split_commutator_pair_points
    (U W C Z U' W' C' Z' : Subgroup G)
    (hc : W ≤ centralizer (C : Set G)) (hd : Disjoint W C)
    (hs : W ⊔ C = U) (hz : Z ≤ C)
    (hc' : W' ≤ centralizer (C' : Set G)) (hd' : Disjoint W' C')
    (hs' : W' ⊔ C' = U') (hz' : Z' ≤ C')
    (hnW : U' ≤ normalizer (W : Set G)) (hnC : U' ≤ normalizer (C : Set G))
    (hnW' : U ≤ normalizer (W' : Set G)) (hnC' : U ≤ normalizer (C' : Set G))
    (hA : ⁅U,U'⁆ ≤ W ⊔ Z) (hA' : ⁅U,U'⁆ ≤ W' ⊔ Z')
    (hZ : Z ≤ ⁅U,U'⁆) (hZ' : Z' ≤ ⁅U,U'⁆) (hZZ : Disjoint Z Z') :
    ⁅C,U'⁆ = Z ∧ ⁅C',U⁆ = Z' ∧ ⁅C,C'⁆ = ⊥ ∧
      ⁅W,C'⁆ = Z' ∧ ⁅W',C⁆ = Z ∧ Z' ≤ W ∧ Z ≤ W' := by
  have hp := split_commutator_point U W C Z U' hc hd hs hz hnW hnC hA hZ
  have hp' := split_commutator_point U' W' C' Z' U hc' hd' hs' hz' hnW' hnC'
    (commutator_comm U U' ▸ hA') (commutator_comm U U' ▸ hZ')
  have hCU : C ≤ U := le_sup_right.trans hs.le
  have hCU' : C' ≤ U' := le_sup_right.trans hs'.le
  have hCC : ⁅C,C'⁆ = ⊥ := by
    apply bot_unique
    exact (le_inf ((commutator_mono le_rfl hCU').trans hp.2.1.le)
      ((commutator_mono hCU le_rfl).trans
        ((commutator_comm U C').trans hp'.2.1).le)).trans (disjoint_iff.mp hZZ).le
  have hWC : ⁅W,C'⁆ = Z' := by
    have he := commutator_sup_of_commuting_factors W C C' hc (hCU'.trans hnC)
    rw [hs,hCC,sup_bot_eq,commutator_comm U C',hp'.2.1] at he
    exact he.symm
  have hWC' : ⁅W',C⁆ = Z := by
    have he := commutator_sup_of_commuting_factors W' C' C hc' (hCU.trans hnC')
    rw [hs',commutator_comm C' C,hCC,sup_bot_eq,commutator_comm U' C,hp.2.1] at he
    exact he.symm
  exact ⟨hp.2.1,hp'.2.1,hCC,hWC,hWC',
    hWC ▸ le_normalizer_iff_commutator_le_left.mp (hCU'.trans hnW),
    hWC' ▸ le_normalizer_iff_commutator_le_left.mp (hCU.trans hnW')⟩

/-- The middle commutator, together with the two point lines, generates the
whole common commutator. This is an equality before any quotient. -/
theorem split_commutator_pair_generation
    (U W C Z U' W' C' Z' : Subgroup G)
    (hc : W ≤ centralizer (C : Set G)) (hs : W ⊔ C = U)
    (hc' : W' ≤ centralizer (C' : Set G)) (hs' : W' ⊔ C' = U')
    (hnC : U' ≤ normalizer (C : Set G))
    (hnC' : U ≤ normalizer (C' : Set G))
    (hCZ : ⁅C,U'⁆ = Z) (hWZ' : ⁅W,C'⁆ = Z') :
    (⁅W,W'⁆ ⊔ Z') ⊔ Z = ⁅U,U'⁆ := by
  have hWU : W ≤ U := le_sup_left.trans hs.le
  have h := commutator_sup_of_commuting_factors W C U' hc hnC
  rw [hs,hCZ] at h
  have h' := commutator_sup_of_commuting_factors W' C' W hc' (hWU.trans hnC')
  rw [hs',commutator_comm U' W,commutator_comm W' W,
    commutator_comm C' W,hWZ'] at h'
  rw [h,h']

end Subgroup
