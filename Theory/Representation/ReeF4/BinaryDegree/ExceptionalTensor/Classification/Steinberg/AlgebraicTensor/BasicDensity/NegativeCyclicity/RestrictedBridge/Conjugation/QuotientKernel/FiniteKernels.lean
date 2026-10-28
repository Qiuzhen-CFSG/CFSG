module

public import Mathlib.RingTheory.SimpleRing.Congr
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Artinian.Module

/-!
# Finiteness of simple quotient kernels

A family of surjections from an Artinian ring to a fixed simple ring has only
finitely many distinct kernels. Choose a minimal finite intersection of the
kernels. Simplicity makes each kernel prime with respect to intersections of
two-sided ideals, so every kernel contains one of the finitely many chosen
kernels. Maximality among proper two-sided ideals makes that containment an
equality. Restriction of scalars gives the finite-dimensional algebra version.

This supplies the finite-orbit step for the connected-conjugation proof of
Steinberg's equation 4.1, independently of Curtis's classification of simple
restricted modules. Source: Steinberg, *Representations of Algebraic Groups*,
Nagoya Math. J. 22 (1963), §4; DOI 10.1017/S0027763000011016.
-/

public section

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge.QuotientKernel

variable {A S ι : Type*} [Ring A] [Ring S] [IsSimpleRing S]

private theorem exists_mem_image_one (f : A →+* S) (hf : Function.Surjective f)
    (I : Ideal A) [I.IsTwoSided] (hI : ¬ I ≤ RingHom.ker f) :
    ∃ x ∈ I, f x = 1 := by
  have : RingHomSurjective f := ⟨hf⟩
  have himage : I.map f = ⊤ := by
    apply ((isSimpleRing_iff_isTwoSided_imp.mp inferInstance).2 (I.map f) inferInstance).resolve_left
    intro hbot
    apply hI
    intro x hx
    have hm : f x ∈ I.map f := Ideal.mem_map_of_mem f hx
    rw [hbot] at hm
    exact hm
  apply (Ideal.mem_map_iff_of_surjective f hf).mp
  rw [himage]
  trivial

private theorem inf_le_kernel (f : A →+* S) (hf : Function.Surjective f)
    (I J : Ideal A) [I.IsTwoSided] [J.IsTwoSided]
    (h : I ⊓ J ≤ RingHom.ker f) : I ≤ RingHom.ker f ∨ J ≤ RingHom.ker f := by
  by_contra hnot
  obtain ⟨hI, hJ⟩ := not_or.mp hnot
  obtain ⟨x, hx, hfx⟩ := exists_mem_image_one f hf I hI
  obtain ⟨y, hy, hfy⟩ := exists_mem_image_one f hf J hJ
  have hz : f (x * y) = 0 := h ⟨I.mul_mem_right y hx, J.mul_mem_left x hy⟩
  rw [map_mul, hfx, hfy, one_mul] at hz
  exact one_ne_zero hz

private theorem kernels_eq_of_le (f g : A →+* S)
    (hf : Function.Surjective f) (h : RingHom.ker f ≤ RingHom.ker g) :
    RingHom.ker f = RingHom.ker g := by
  apply le_antisymm h
  by_contra hn
  obtain ⟨x, hx, hfx⟩ := exists_mem_image_one f hf (RingHom.ker g) hn
  have hm : x - 1 ∈ RingHom.ker f := by
    change f (x - 1) = 0
    rw [map_sub, hfx, map_one, sub_self]
  have hz : g (x - 1) = 0 := h hm
  have hx' : g x = 0 := hx
  rw [map_sub, hx', map_one, zero_sub, neg_eq_zero] at hz
  exact one_ne_zero hz

private theorem finset_inf_le_kernel (f : A →+* S) (hf : Function.Surjective f)
    (J : ι → Ideal A) [∀ i, (J i).IsTwoSided] (s : Finset ι)
    (h : s.inf J ≤ RingHom.ker f) : ∃ i ∈ s, J i ≤ RingHom.ker f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz : f 1 = 0 := h (by simp)
    simp at hz
  | @insert i s hi ih =>
    rw [Finset.inf_insert] at h
    have : (s.inf J).IsTwoSided := ⟨fun a hb =>
      Submodule.mem_finsetInf.mpr fun j hj =>
        (J j).mul_mem_right a (Submodule.mem_finsetInf.mp hb j hj)⟩
    rcases inf_le_kernel f hf (J i) (s.inf J) h with hle | hle
    · exact ⟨i, Finset.mem_insert_self _ _, hle⟩
    · obtain ⟨j, hj, hle⟩ := ih hle
      exact ⟨j, Finset.mem_insert_of_mem hj, hle⟩

/-- An Artinian ring has only finitely many distinct kernels in a family of
surjections to a fixed simple ring. -/
theorem finite_range_ring_kernels [IsArtinianRing A]
    (f : ι → A →+* S) (hf : ∀ i, Function.Surjective (f i)) :
    (Set.range fun i => RingHom.ker (f i)).Finite := by
  classical
  obtain ⟨s, hs⟩ := Finset.exists_inf_le (fun i => RingHom.ker (f i))
  apply ((s.finite_toSet).image (fun i => RingHom.ker (f i))).subset
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, hj, hji⟩ := finset_inf_le_kernel (f i) (hf i)
    (fun j => RingHom.ker (f j)) s (hs i)
  exact ⟨j, hj, kernels_eq_of_le (f j) (f i) (hf j) hji⟩

variable {F : Type*} [Field F] [Algebra F A] [Algebra F S]

/-- The linear kernels of such a family in a finite-dimensional algebra are finite. -/
theorem finite_range_linear_kernels [FiniteDimensional F A]
    (f : ι → A →ₐ[F] S) (hf : ∀ i, Function.Surjective (f i)) :
    (Set.range fun i => LinearMap.ker (f i).toLinearMap).Finite := by
  have : IsArtinianRing A := isArtinian_of_tower F inferInstance
  have hfinite := finite_range_ring_kernels (fun i => (f i).toRingHom) hf
  convert hfinite.image (fun I : Ideal A => I.restrictScalars F) using 1
  ext I
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨RingHom.ker (f i).toRingHom, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge.QuotientKernel
