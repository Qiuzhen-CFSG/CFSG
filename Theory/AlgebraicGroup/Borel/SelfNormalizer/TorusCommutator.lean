module

public import Theory.AlgebraicGroup.Borel.SelfNormalizer.TorusReduction
public import Theory.AlgebraicGroup.Automorphisms.Lang.CommutativeSurjectivity

/-!
# The torus commutator in the finite fixed-point case

For a torus normalizer point `n`, conjugation restricts to a regular torus
endomorphism. If its fixed points are finite, the commutative Lang theorem
makes `s ↦ n * s * n⁻¹ * s⁻¹` surjective on the torus. Thus the torus lies
in the derived subgroup of every subgroup containing the torus and `n`.

This proves the commutator step of Borel, *Linear Algebraic Groups*,
Theorem 11.16(iii), `refs/KGroup/Bor1/Chapter4.tex`, line 229. The subsequent
Chevalley-line and complete-homogeneous-space argument is not asserted here.
-/

universe u

namespace Theory.AlgebraicGroup.BorelSelfNormalizer

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- In source case (iii), every torus point is a commutator with the chosen
normalizer element. This is a finite-kernel endomorphism of the actual torus. -/
public theorem exists_torus_commutator_of_finite_fixedPoints
    (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (n : Variety.Point G) (hn : n ∈ T.normalizer.toSubgroup)
    (hfixed : (fixedTorusPoints T n).Finite)
    (t : Variety.Point G) (ht : t ∈ T.toSubgroup) :
    ∃ s : Variety.Point G, s ∈ T.toSubgroup ∧ n * s * n⁻¹ * s⁻¹ = t := by
  let c : AlgebraicGroup.Morphism G G :=
    { toVariety := AlgebraicGroup.conjugationByMorphism G n
      map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
      map_mul := by
        intro x y
        simp only [AlgebraicGroup.conjugationByMorphism_apply]
        group }
  have hmap (x : Variety.Point T.carrierVariety) :
      (c.comp T.inclusion).onPoints x ∈ T.toSubgroup :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp (T.pointEquiv x).property
  let sigma := (c.comp T.inclusion).codRestrictClosedSubgroup T hmap
  have hsigma (x : Variety.Point T.carrierVariety) :
      T.inclusion.onPoints (sigma.onPoints x) = n * T.inclusion.onPoints x * n⁻¹ := by
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
    rfl
  have hfinite : Finite {x : Variety.Point T.carrierVariety | sigma.onPoints x = x} := by
    let f : {x : Variety.Point T.carrierVariety | sigma.onPoints x = x} →
        fixedTorusPoints T n := fun x =>
      ⟨T.inclusion.onPoints x.1, (T.pointEquiv x.1).property, by
        have h := hsigma x.1
        rw [x.property] at h
        exact (mul_inv_eq_iff_eq_mul).mp h.symm⟩
    let : Finite (fixedTorusPoints T n) := hfixed.to_subtype
    exact Finite.of_injective f (by
      intro x y h
      apply Subtype.ext
      exact T.inclusion_injective
        (congrArg (fun z : fixedTorusPoints T n => z.val) h))
  let tT := T.pointEquiv.symm ⟨t, ht⟩
  have htT : T.inclusion.onPoints tT = t :=
    congrArg Subtype.val (T.pointEquiv.apply_symm_apply _)
  obtain ⟨s, hs⟩ := langMorphism_surjective_of_connected_commutative
    sigma hT.isConnected hT.isMulCommutative hfinite tT⁻¹
  refine ⟨T.inclusion.onPoints s, (T.pointEquiv s).property, ?_⟩
  have h := congrArg T.inclusion.onPoints hs
  simp only [langMorphism_apply, map_mul, map_inv, hsigma, htT] at h
  have hinv := congrArg Inv.inv h
  simpa only [mul_inv_rev, inv_inv] using hinv

/-- The fixed-finite torus lies in the derived subgroup of any subgroup
containing it and the chosen normalizer point, as used for `N = N_G(B)`
in Borel 11.16(iii). -/
public theorem torus_le_commutator_of_finite_fixedPoints
    (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (n : Variety.Point G) (hn : n ∈ T.normalizer.toSubgroup)
    (hfixed : (fixedTorusPoints T n).Finite)
    (N : Subgroup (Variety.Point G)) (hnN : n ∈ N) (hTN : T.toSubgroup ≤ N) :
    T.toSubgroup ≤ ⁅N, N⁆ := by
  intro t ht
  obtain ⟨s, hs, hst⟩ := exists_torus_commutator_of_finite_fixedPoints T hT n hn hfixed t ht
  have h := Subgroup.commutator_mem_commutator hnN (hTN hs)
  change n * s * n⁻¹ * s⁻¹ ∈ ⁅N, N⁆ at h
  rwa [hst] at h

end Theory.AlgebraicGroup.BorelSelfNormalizer
