module

public import Theory.Mathieu.M12.Properties.SylowAutomorphisms
public import Theory.Mathieu.M12.Properties.SylowAutomorphismGroup.Coordinates
public import Theory.GroupTheory.PrimePowerGenerated
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# The automorphism fixer of the second M₁₂ parabolic's three-residual

The residual contains the moving cubic, all its conjugates in the parabolic,
and the natural four. An element centralizing it therefore lies in the marked
Sylow subgroup. A kernel-checked calculation on its 64 established coordinates
shows that commuting with the cubic and its three generator conjugates forces
identity. No new enumeration of M₁₂ or its full automorphism group is needed.

An automorphism fixing this residual pointwise then fixes its normalizer
pointwise. The existing Sylow-fixer theorem leaves identity and conjugation
by z; the latter does not fix the moving cubic. This covers the full abstract
automorphism group without assuming an automorphism model or local placement.

Source: Aschbacher–Smith, 15.3.43, sporadic paragraph, printed p.1140.
The marked elements and certified Sylow coordinates retain their attribution
in `SmallParabolicPair.Seeds` and `Properties.SylowAutomorphismGroup.Coordinates`.
-/

public section
open Subgroup
namespace Sporadic.Mathieu.M12SmallPair
open SylowAutomorphismGroup

private noncomputable abbrev R : Subgroup M12 :=
  (primePowerGenerated 3 secondParabolic).map secondParabolic.subtype

private theorem cubic_mem : movingActor ∈ R := by
  refine ⟨⟨movingActor, movingActor_mem⟩, mem_primePowerGenerated_of_pow (n := 1) ?_, rfl⟩
  apply Subtype.ext
  change movingActor ^ 3 = 1
  simpa only [movingActor_order] using pow_orderOf_eq_one movingActor

private theorem normalizes_R : secondParabolic ≤ normalizer (R : Set M12) :=
  secondParabolic.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image secondParabolic (primePowerGenerated 3 secondParabolic))

private theorem conjugate_cubic_mem (t : M12) (ht : t ∈ secondParabolic) :
    t * movingActor * t⁻¹ ∈ R :=
  (mem_set_normalizer_iff.mp (normalizes_R ht) movingActor).mp cubic_mem

private theorem z_mem_R : z ∈ R := by
  have hzP : z ∈ secondParabolic := natural.le_normalizer z_mem_natural
  have h := R.mul_mem (R.mul_mem cubic_mem
    (R.mul_mem cubic_mem (R.inv_mem (conjugate_cubic_mem z hzP)))) (R.inv_mem cubic_mem)
  have he : movingActor * (movingActor * (z * movingActor * z⁻¹)⁻¹) * movingActor⁻¹ = z := by
    decide +kernel
  rwa [he] at h

private theorem natural_le_R : natural ≤ R := by
  apply (closure_le _).mpr
  rintro x (rfl | rfl)
  · exact z_mem_R
  · have h := R.mul_mem (R.mul_mem cubic_mem z_mem_R) (R.inv_mem cubic_mem)
    rwa [movingActor_conjugates_z] at h

set_option maxRecDepth 100000 in
private theorem centralizer_check : ∀ i : Fin 64,
    let x : M12 := element i
    movingActor * x = x * movingActor →
    (∀ j : Fin 3, let t : M12 := generator j
      (t * movingActor * t⁻¹) * x = x * (t * movingActor * t⁻¹)) → x = 1 := by
  decide +kernel

/-- The three-residual of the natural-four normalizer has trivial centralizer in M₁₂. -/
theorem centralizer_second_threeResidual :
    centralizer ((primePowerGenerated 3 secondParabolic).map
      secondParabolic.subtype : Set M12) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hxS : x ∈ sylowCandidate := by
    refine ⟨?_, ?_⟩
    · exact mem_centralizer_singleton_iff.mpr (hx z z_mem_R).symm
    · exact centralizer_le_normalizer (natural : Set M12) (centralizer_le natural_le_R hx)
  obtain ⟨i, hi⟩ := element_surjective ⟨x, hxS⟩
  have he : (element i : M12) = x := congrArg Subtype.val hi
  have hc := centralizer_check i (he ▸ hx movingActor cubic_mem) (by
    intro j
    exact he ▸ hx _ (conjugate_cubic_mem (generator j) (generator j).property.2))
  exact he ▸ hc

private theorem fixes_normalizer (f : MulAut M12) (hf : ∀ x ∈ R, f x = x)
    (s : M12) (hs : s ∈ secondParabolic) : f s = s := by
  have hd : s⁻¹ * f s ∈ centralizer (R : Set M12) := by
    intro x hx
    have hn : s * x * s⁻¹ ∈ R :=
      (mem_set_normalizer_iff.mp (normalizes_R hs) x).mp hx
    have hconj := hf _ hn
    simp only [map_mul, map_inv, hf x hx] at hconj
    have he : (s⁻¹ * f s) * x * (s⁻¹ * f s)⁻¹ = x := by
      calc
        _ = s⁻¹ * (f s * x * (f s)⁻¹) * s := by group
        _ = s⁻¹ * (s * x * s⁻¹) * s := by rw [hconj]
        _ = x := by group
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  rw [centralizer_second_threeResidual, mem_bot] at hd
  exact (inv_mul_eq_one.mp hd).symm

/-- The pointwise fixer of the marked three-residual in the full automorphism group is trivial. -/
theorem eq_one_of_fixes_second_threeResidual (f : MulAut M12)
    (hf : ∀ x ∈ (primePowerGenerated 3 secondParabolic).map secondParabolic.subtype,
      f x = x) : f = 1 := by
  rcases SylowAutomorphisms.eq_one_or_conj_of_fixes_sylow f
    (fun x hx => fixes_normalizer f hf x hx.2) with h | h
  · exact h
  · have he := hf movingActor cubic_mem
    rw [h] at he
    have hne : MulAut.conj z movingActor ≠ movingActor := by decide +kernel
    exact (hne he).elim

end Sporadic.Mathieu.M12SmallPair
