module
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Coprime control of a conjugate core join

Suppose Q centralizes W and has index two in an automorphism-invariant
subgroup S. If the automorphism moves W outside Q, its conjugate centralizer
has index two as well. An element of W in the other coset gives
Q = W C_Q(Wᵉ), without any ambient normality assumption.

For the invariance step, let S = Q Wᵉ inside T and let a coprime actor B
normalize Q and W, with [Q,B] ≤ W. If e preserves T and B and C_T(B) ≤ S,
then coprime decomposition and the order-two quotient give
S = W C_T(B) = [W,B] C_T(B). The inclusion [Wᵉ,B] ≤ [W,B] is equality
by finiteness, so e preserves S.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, 3.3.31, printed p.602. The literal source application is in
FusionReducibleNormalizerBlockCentralizerAlternatingGeometry.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

private theorem map_centralizer (W : Subgroup G) (e : G ≃* G) :
    (centralizer (W : Set G)).map e.toMonoidHom =
      centralizer (W.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

/-- Crossing an index-two conjugate centralizer supplies the whole original
centralizer from W and its fixed subgroup on Wᵉ. -/
theorem eq_sup_inf_centralizer_of_invariant_index_two
    (S Q W : Subgroup G) (e : G ≃* G)
    (hQ : Q = S ⊓ centralizer (W : Set G)) (hWQ : W ≤ Q)
    (hS : S.map e.toMonoidHom = S) (hi : Q.relIndex S = 2)
    (hmove : ¬ W.map e.toMonoidHom ≤ Q) :
    Q = W ⊔ (Q ⊓ centralizer (W.map e.toMonoidHom : Set G)) := by
  classical
  let Q' := Q.map e.toMonoidHom
  have hQS : Q ≤ S := hQ.le.trans inf_le_left
  have hQ' : Q' = S ⊓ centralizer (W.map e.toMonoidHom : Set G) := by
    rw [show Q' = Q.map e.toMonoidHom from rfl, hQ,
      map_inf _ _ _ e.injective, hS, map_centralizer]
  have hi' : Q'.relIndex S = 2 := by
    rw [← hS, relIndex_map_map_of_injective _ _ e.injective]
    exact hi
  have hWnot : ¬ W ≤ Q' := by
    intro hW
    apply hmove
    rw [hQ]
    apply le_inf ((map_mono (hWQ.trans hQS)).trans_eq hS)
    exact le_centralizer_iff.mp (hW.trans (hQ'.le.trans inf_le_right))
  obtain ⟨w, hw, hw'⟩ := SetLike.not_le_iff_exists.mp hWnot
  apply le_antisymm ?_ (sup_le hWQ inf_le_left)
  intro q hq
  by_cases hq' : q ∈ Q'
  · exact mem_sup_right ⟨hq, (hQ'.le hq').2⟩
  · have hdiff : q * w⁻¹ ∈ Q' := by
      apply ((Q'.subgroupOf S).mul_mem_iff_of_index_two hi'
        (a := (⟨q, hQS hq⟩ : S))
        (b := (⟨w, hQS (hWQ hw)⟩ : S)⁻¹)).mpr
      change q ∈ Q' ↔ w⁻¹ ∈ Q'
      simp only [inv_mem_iff, hq', hw']
    have hm : q * w⁻¹ ∈ W ⊔ (Q ⊓ centralizer (W.map e.toMonoidHom : Set G)) :=
      mem_sup_right ⟨Q.mul_mem hq (Q.inv_mem (hWQ hw)), (hQ'.le hdiff).2⟩
    simpa only [inv_mul_cancel_right] using mul_mem hm (mem_sup_left hw)

variable [Finite G]

/-- A coprime actor whose T-centralizer lies in the conjugate join makes
that join invariant. The index and centralizer containment are genuine inputs. -/
theorem map_join_eq_of_coprime_centralizer_cover
    (T Q W B : Subgroup G) (e : G ≃* G)
    (hQT : Q ≤ T) (hWQ : W ≤ Q) (hTW : T ≤ normalizer (W : Set G))
    (hBQ : B ≤ normalizer (Q : Set G)) (hBW : B ≤ normalizer (W : Set G))
    (hT : T.map e.toMonoidHom = T) (hB : B.map e.toMonoidHom = B)
    (hsolv : Group.IsSolvable Q) (hcop : Nat.Coprime (Nat.card B) (Nat.card Q))
    (hcomm : ⁅Q, B⁆ ≤ W)
    (hi : Q.relIndex (Q ⊔ W.map e.toMonoidHom) = 2)
    (hcentral : T ⊓ centralizer (B : Set G) ≤ Q ⊔ W.map e.toMonoidHom) :
    (Q ⊔ W.map e.toMonoidHom).map e.toMonoidHom = Q ⊔ W.map e.toMonoidHom := by
  let W' := W.map e.toMonoidHom
  let S := Q ⊔ W'
  let C := T ⊓ centralizer (B : Set G)
  let U := ⁅W, B⁆
  let := hsolv
  have hWsolv : Group.IsSolvable W :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hWQ)
  let := hWsolv
  have hW'solv : Group.IsSolvable W' :=
    Group.isSolvable_of_surjective
      (f := (W.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
      (W.equivMapOfInjective e.toMonoidHom e.injective).surjective
  have hWcop : Nat.Coprime (Nat.card B) (Nat.card W) :=
    hcop.of_dvd_right (card_dvd_of_le hWQ)
  have hW'cop : Nat.Coprime (Nat.card B) (Nat.card W') := by
    simpa only [W', card_map_of_injective (f := e.toMonoidHom) e.injective] using hWcop
  have hW'T : W' ≤ T := (map_mono (hWQ.trans hQT)).trans_eq hT
  have hBW' : B ≤ normalizer (W' : Set G) := by
    have hh := map_mono (f := e.toMonoidHom) hBW
    rw [hB, map_equiv_normalizer_eq] at hh
    exact hh
  have hBS : B ≤ normalizer (S : Set G) :=
    (le_inf hBQ hBW').trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hW'comm : ⁅W', B⁆ ≤ Q :=
    (commutator_mono le_sup_right le_rfl).trans
      (commutator_le_of_normalized_index_two S Q B le_sup_left hi hBS hBQ)
  have hQcover : Q ≤ W ⊔ C := by
    rw [eq_commutator_sup_centralizer_of_solvable_coprime Q B hBQ hsolv hcop]
    exact sup_le (hcomm.trans le_sup_left)
      ((inf_le_inf_right _ hQT).trans le_sup_right)
  have hW'cover : W' ≤ Q ⊔ C := by
    rw [eq_commutator_sup_centralizer_of_solvable_coprime W' B hBW' hW'solv hW'cop]
    exact sup_le (hW'comm.trans le_sup_left)
      ((inf_le_inf_right _ hW'T).trans le_sup_right)
  have hScover : S = W ⊔ C := by
    apply le_antisymm
    · exact sup_le hQcover (hW'cover.trans (sup_le hQcover le_sup_right))
    · exact sup_le (hWQ.trans le_sup_left) hcentral
  have hCnorm : C ≤ normalizer (U : Set G) := by
    intro c hc
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hTW hc.1),
      mem_normalizer_iff_map_conj_eq.mp ((centralizer_le_normalizer (B : Set G)) hc.2)]
  have hSC : S ≤ normalizer (U : Set G) := by
    rw [hScover]
    exact sup_le (normalizer_commutator_ge_left W B) hCnorm
  have hSB : ⁅S, B⁆ ≤ U := by
    rw [hScover]
    exact commutator_sup_le_of_relative_normal S W C B U hSC
      (hWQ.trans le_sup_left) hcentral le_rfl
      ((commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le)
  have hUmap : U.map e.toMonoidHom = U := by
    apply eq_of_le_of_card_ge
    · rw [show U = ⁅W, B⁆ from rfl, map_commutator, hB]
      exact (commutator_mono le_sup_right le_rfl).trans hSB
    · exact (card_map_of_injective (f := e.toMonoidHom) e.injective).ge
  have hCmap : C.map e.toMonoidHom = C := by
    rw [show C = T ⊓ centralizer (B : Set G) from rfl,
      map_inf _ _ _ e.injective, hT, map_centralizer, hB]
  have hSsplit : S = U ⊔ C := by
    apply le_antisymm
    · rw [hScover, eq_commutator_sup_centralizer_of_solvable_coprime W B hBW hWsolv hWcop]
      exact sup_le (sup_le le_sup_left
        ((inf_le_inf_right _ (hWQ.trans hQT)).trans le_sup_right)) le_sup_right
    · exact sup_le ((le_normalizer_iff_commutator_le_left.mp hBW).trans
        (hWQ.trans le_sup_left)) hcentral
  change S.map e.toMonoidHom = S
  rw [hSsplit, Subgroup.map_sup, hUmap, hCmap]

end Subgroup
