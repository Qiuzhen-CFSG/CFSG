module

public import Theory.AlgebraicGroup.Solvable.TorusDecomposition
public import Theory.AlgebraicGroup.Tori.Maximal.theorem_1_4_3_b

/-!
# Pointwise conjugacy from agreement modulo the unipotent radical

In a connected solvable group, two torus homomorphisms agreeing modulo the
unipotent radical are conjugate pointwise by a radical element when the first
image lies in a specified torus complement. Conjugate a maximal torus
containing the second image into that complement; injectivity modulo the
radical then identifies every point. A triangular presentation supplies an
actual torus-valued morphism with exactly the unipotent-radical kernel.

This is the solvable conjugacy step in Borel, *Linear Algebraic Groups*, §11.15.
-/

namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

public theorem torus_homomorphisms_conjugate_of_quotient_eq
    {G T Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup T] [AlgebraicGroup Q]
    (hG : Variety.IsConnected G) (hsolv : Group.IsSolvable (Variety.Point G))
    (U A : ClosedSubgroup G) (hU : IsUnipotentRadicalSubgroup U)
    (hA : IsTorusComplement A U) (hT : IsTorus T)
    (q : AlgebraicGroup.Morphism G Q) (hker : q.kernel = U.toSubgroup)
    (i j : AlgebraicGroup.Morphism T G) (hi : i.imageClosedSubgroup ≤ A)
    (hij : ∀ t, q.onPoints (i.onPoints t) = q.onPoints (j.onPoints t)) :
    ∃ u : Variety.Point G, u ∈ U.toSubgroup ∧
      ∀ t, j.onPoints t = u⁻¹ * i.onPoints t * u := by
  obtain ⟨R, hR, hjR⟩ := exists_maximalTorus_containing j.imageClosedSubgroup
    (morphism_image_isTorus j hT)
  obtain ⟨u, hu, hRA⟩ := maximalTorus_conjugate_to_torusComplement_by_unipotentRadical
    hsolv hG U A R hU hA hR
  have hqu : q.onPoints u = 1 := by
    change u ∈ q.kernel
    rwa [hker]
  have hinj {a b : Variety.Point G} (ha : a ∈ A.toSubgroup) (hb : b ∈ A.toSubgroup)
      (he : q.onPoints a = q.onPoints b) : a = b := by
    have hab : a * b⁻¹ ∈ A.toSubgroup ⊓ U.toSubgroup := by
      refine ⟨A.toSubgroup.mul_mem ha (A.toSubgroup.inv_mem hb), ?_⟩
      rw [← hker]
      change q.onPoints (a * b⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    rw [hA.2.2] at hab
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hab)
  refine ⟨u, hu, ?_⟩
  intro t
  have hjA : u * j.onPoints t * u⁻¹ ∈ A.toSubgroup := by
    rw [← hRA]
    change u * j.onPoints t * u⁻¹ ∈ R.conjugate u
    rw [R.mem_conjugate_iff]
    have hred : u⁻¹ * (u * j.onPoints t * u⁻¹) * u = j.onPoints t := by group
    rw [hred]
    exact hjR ⟨t, rfl⟩
  have he : u * j.onPoints t * u⁻¹ = i.onPoints t := by
    apply hinj hjA (hi ⟨t, rfl⟩)
    rw [map_mul, map_mul, map_inv, hqu, one_mul, inv_one, mul_one]
    exact (hij t).symm
  calc
    j.onPoints t = u⁻¹ * (u * j.onPoints t * u⁻¹) * u := by group
    _ = u⁻¹ * i.onPoints t * u := by rw [he]

public theorem exists_torus_morphism_kernel_unipotentRadical
    {G : Variety k} [AlgebraicGroup G]
    (hG : Variety.IsConnected G) (hsolv : Group.IsSolvable (Variety.Point G))
    (U : ClosedSubgroup G) (hU : IsUnipotentRadicalSubgroup U) :
    ∃ (n : ℕ) (q : AlgebraicGroup.Morphism G (dVariety k n)), q.kernel = U.toSubgroup := by
  obtain ⟨n, hn, L, ⟨e⟩⟩ := exists_iso_closedSubgroup_tVariety_of_isSolvable_isConnected hsolv hG
  let P : TriangularPresentation G := ⟨n, hn, L, e⟩
  refine ⟨n, P.diagonalMorphism, ?_⟩
  apply SetLike.coe_injective
  ext x
  exact (P.mem_unipotentRadical_iff_characteristicFree x).trans (hU x).symm
end Theory.AlgebraicGroup
