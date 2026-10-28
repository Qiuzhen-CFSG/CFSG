module

public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry
public import Theory.Mathieu.M12.Properties.SylowAutomorphismGroup.Coordinates
public import Theory.GroupTheory.SubgroupCenterImageBound

/-!
# Involution squares and full Sylow centers in M₁₂

In the checked 64-element Sylow model, every nonidentity involution square
is one of the three involutions in the marked natural four. Its cubic actor
fuses those three elements. Sylow conjugacy therefore makes every involution
square in M₁₂ conjugate to the marked central involution. The existing center
membership theorem identifies the entire Sylow center with its cyclic subgroup.

This is the intrinsic fusion calculation used in Aschbacher–Smith, combined
manuscript of 1 March 2004, proof of 16.3.4, printed p.1178. The permutations
and word coordinates come from the attributed M₁₂ small-parabolic construction;
the finite certificate below is checked by the kernel.
-/

public section
open Subgroup
namespace Sporadic.Mathieu.M12SylowCenters
open M12SmallPair
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

theorem marked_center :
    (center sylowCandidate).map sylowCandidate.subtype = zpowers z := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change (x : M12) ∈ zpowers z
    rcases (sylowCandidate_center_mem x).mp hx with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact mem_zpowers _
  · apply zpowers_le.mpr
    exact ⟨⟨z, core_le_sylowCandidate z_mem_core⟩,
      (sylowCandidate_center_mem _).mpr (Or.inr rfl), rfl⟩

private theorem square_check : ∀ j : Fin 64,
    let x : M12 := SylowAutomorphismGroup.element j
    x ^ 4 = 1 → x ^ 2 ≠ 1 →
      ∃ k : Fin 3, (MulAut.conj (movingActor ^ k.val)) z = x ^ 2 := by
  decide +kernel

/-- Every involution which is a square in M₁₂ is conjugate to the marked Sylow center. -/
theorem square_involution_conjugate (x : M12) (hx : orderOf x = 2)
    (hsq : ∃ y : M12, y ^ 2 = x) : ∃ g : M12, (MulAut.conj g) z = x := by
  obtain ⟨y, hy⟩ := hsq
  have hy4 : y ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hy, ← hx, pow_orderOf_eq_one]
  have hp : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card_dvd_pow (n := 2) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hy4)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 P commonSylow
  have hmem : (MulAut.conj g) y ∈ sylowCandidate := by
    change (MulAut.conj g) y ∈ (commonSylow : Subgroup M12)
    rw [← hg]
    exact mem_map_of_mem _ (hP (mem_zpowers y))
  obtain ⟨j, hj⟩ := SylowAutomorphismGroup.element_surjective ⟨_, hmem⟩
  have hj' : (SylowAutomorphismGroup.element j : M12) = (MulAut.conj g) y :=
    congrArg Subtype.val hj
  obtain ⟨k, hk⟩ := square_check j
    (by rw [hj', ← map_pow, hy4, map_one])
    (by rw [hj', ← map_pow, hy]
        intro h
        have he := (MulAut.conj g).injective (h.trans (map_one _).symm)
        simp [he] at hx)
  refine ⟨g⁻¹ * movingActor ^ k.val, ?_⟩
  have he : (MulAut.conj (g⁻¹ * movingActor ^ k.val)) z =
      (MulAut.conj g).symm ((MulAut.conj (movingActor ^ k.val)) z) := by
    simp only [MulAut.conj_apply, mul_inv_rev]
    change _ = g⁻¹ * _ * (g⁻¹)⁻¹
    group
  rw [he, hk, hj', ← map_pow, hy, MulEquiv.symm_apply_apply]

/-- The center of the actual Sylow subgroup is transported, without an omega operation. -/
theorem exists_sylow_center_of_square (x : M12) (hx : orderOf x = 2)
    (hsq : ∃ y : M12, y ^ 2 = x) :
    ∃ S : Sylow 2 M12, (center S).map (S : Subgroup M12).subtype = zpowers x := by
  obtain ⟨g, hg⟩ := square_involution_conjugate x hx hsq
  let e := MulAut.conj g
  refine ⟨commonSylow.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (center (sylowCandidate.map e.toMonoidHom)).map
    (sylowCandidate.map e.toMonoidHom).subtype = _
  rw [← map_subgroup_center_eq e.toMonoidHom e.injective, marked_center, MonoidHom.map_zpowers]
  exact congrArg zpowers hg
end Sporadic.Mathieu.M12SylowCenters
