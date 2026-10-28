module

public import Theory.GroupTheory.PerfectCentralCoverSylowCenterCriterion
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner

/-!
# The direct Sylow-center calculation for binary PSL₂ covers

The diagonal torus of SL₂ scales the additive root parameter by squares.
Squaring is bijective in a finite field of characteristic two, so its actual
normalizer is transitive on the nonidentity root elements. The root group is
abelian. The generic transfer criterion therefore identifies the center of
every Sylow of a perfect central double cover with its kernel.

Use the characteristic-two SL₂/PSL₂ isomorphism and the given covering map.
This includes PSL₂(4), without classifying its cover as SL₂(5).
Source: GLS4, Chapter 4, Lemma 2.8(c).
-/

namespace BenderSuzuki.ZD.DirectSylowCenters
open Converse Linear _root_.BenderSuzuki.MatrixGroups Subgroup PerfectCentralCovering
open scoped IsMulCommutative
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

public theorem linear_root_center_action : SylowCenterAction (Unip K) := by
  have hnorm : Borel K ≤ normalizer (Unip K : Set (SL2 K)) := by
    intro g hg u
    constructor
    · exact Unip_conj_mem hg
    · intro hu
      have hi := Unip_conj_mem ((Borel K).inv_mem hg) hu
      change u ∈ Unip K
      simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_left,
        mul_assoc, inv_mul_cancel, mul_one] using hi
  refine ⟨?_, Or.inl ?_⟩
  · intro z w hz hw
    obtain ⟨a, ha⟩ := (mem_Unip_iff ((z : Unip K) : SL2 K)).mp (z : Unip K).property
    obtain ⟨b, hb⟩ := (mem_Unip_iff ((w : Unip K) : SL2 K)).mp (w : Unip K).property
    have ha0 : a ≠ 0 := by
      intro h
      apply hz
      apply Subtype.ext
      apply Subtype.ext
      rw [ha, h]
      exact (uniHom K).map_one
    have hb0 : b ≠ 0 := by
      intro h
      apply hw
      apply Subtype.ext
      apply Subtype.ext
      rw [hb, h]
      exact (uniHom K).map_one
    obtain ⟨r, hr⟩ := (Finite.surjective_of_injective (CharTwo.sq_injective (R := K))) (b / a)
    change r ^ 2 = b / a at hr
    have hr0 : r ≠ 0 := by
      intro h
      rw [h, zero_pow (by decide)] at hr
      exact (div_ne_zero hb0 ha0) hr.symm
    let u : Kˣ := Units.mk0 r hr0
    have hut : tor u ∈ Borel K := by rw [mem_Borel_iff]; simp
    refine ⟨⟨tor u, hnorm hut⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change tor u * ((z : Unip K) : SL2 K) * (tor u)⁻¹ = ((w : Unip K) : SL2 K)
    rw [ha, hb, Borel_conj_uni hut]
    congr 1
    change r ^ 2 * a = b
    rw [hr, div_mul_cancel₀ _ ha0]
  · change IsMulCommutative (uniHom K).range
    infer_instance

public theorem linear_exists_sylow_center_action :
    ∃ Q : Sylow 2 (SL2 K), SylowCenterAction (Q : Subgroup (SL2 K)) := by
  let Q := Matrix.SpecialLinearGroup.upperUnipotentSylow K 2
  have hQ : (Q : Subgroup (SL2 K)) = Unip K := by
    change Matrix.SpecialLinearGroup.upperUnipotent K = Unip K
    ext g
    rw [Matrix.SpecialLinearGroup.mem_upperUnipotent, mem_Unip_iff]
    simp only [upper_transvection_eq_uni, eq_comm]
  exact ⟨Q, hQ ▸ linear_root_center_action⟩

public theorem linear_cover_sylow_center
    {E B : Type*} [Group E] [Finite E] [Group B]
    (f : Cover E B) (hcard : Nat.card f.toMonoidHom.ker = 2)
    (e : B ≃* PSL2MatrixGroup K) (P : Sylow 2 E) :
    (center P).map (P : Subgroup E).subtype = f.toMonoidHom.ker := by
  let j : SL2 K ≃* PSL2MatrixGroup K :=
    MulEquiv.ofBijective (pi K) ⟨pi_injective, pi_surjective⟩
  obtain ⟨Q, hQ⟩ := linear_exists_sylow_center_action (K := K)
  exact f.sylow_center_eq_kernel_of_model_sylow hcard (e.trans j.symm) Q hQ P
end BenderSuzuki.ZD.DirectSylowCenters
