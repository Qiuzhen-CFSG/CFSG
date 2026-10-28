module
public import Theory.Representation.PSL3Two.DualResidualPlane
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SubgroupPartitionCounting
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# Numerical bounds from a marked natural and dual pair

A relatively normalized L3(2) quotient supplies an eight-element Sylow image.
For the section bound, a specified Singer matrix has zero fixed space on both
three-dimensional constituents. If its lift centralizes X, separation of the
supports forces X to meet their join only in the central line. Counting the
literal sections then gives index at least 64.

Source: Aschbacher--Smith, 14.6.20--22 and printed p.1042. The source consumer
uses generalized-Fitting centrality on the involutions of the core center.
-/

@[expose] public section
open Subgroup Representation Matrix
open scoped Pointwise commutatorElement
namespace Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents
variable {G : Type*} [Group G] [Finite G]

theorem core_index_bound (T : Sylow 2 G) (Q L : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G))
    (f : L →* SL) (hf : Function.Surjective f)
    (hk : Q.subgroupOf L ≤ f.ker) :
    8 ≤ Q.relIndex (T : Subgroup G) := by
  obtain ⟨S,hS⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T L hn
  let P : Sylow 2 SL := S.mapSurjective hf
  have hcard : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity, Matrix.PSL3Two.card_SL]
    decide +kernel
  have he : f.ker.relIndex (S : Subgroup L) = 8 := by
    rw [relIndex_ker]
    exact hcard
  have hle : 8 ≤ (Q.subgroupOf L).relIndex ((T : Subgroup G).subgroupOf L) := by
    rw [← hS, ← he]
    exact relIndex_le_of_le_left hk (Subgroup.index_ne_zero_of_finite)
  have he' : (Q.subgroupOf L).relIndex ((T : Subgroup G).subgroupOf L) =
      Q.relIndex ((T : Subgroup G) ⊓ L) := by
    rw [← relIndex_subgroupOf (H := Q) (L := L) (show (T : Subgroup G) ⊓ L ≤ L from inf_le_right)]
    congr 1
    ext x
    simp only [mem_subgroupOf, mem_inf, and_iff_left x.property]
  rw [he'] at hle
  exact hle.trans (relIndex_le_of_le_right inf_le_left Subgroup.index_ne_zero_of_finite)

def naturalDualSinger : SL := ⟨!![0,0,1; 0,1,1; 1,1,0], by decide⟩

theorem naturalDualSinger_natural (v : V) (hv : specialLinearNatural 3 naturalDualSinger v = v) : v=0 := by
  have h : ∀ v : V, specialLinearNatural 3 naturalDualSinger v = v → v = 0 := by decide +kernel
  exact h v hv

theorem naturalDualSinger_dual (v : V) (hv : fullDual naturalDualSinger v = v) : v=0 := by
  have h : ∀ v : V, fullDual naturalDualSinger v = v → v = 0 := by decide +kernel
  exact h v hv

variable {N A B Z X : Subgroup G}

omit [Finite G] in
theorem pair_fixed_intersection (f : N →* SL)
    (a : BinaryConjugationSection N A Z ((specialLinearNatural 3).comp f))
    (b : BinaryConjugationSection N B Z (fullDual.comp f))
    (hsep : A ⊓ B ≤ Z) (hbn : B ≤ normalizer (A : Set G))
    (k : N) (hk : f k = naturalDualSinger)
    (hX : (k : G) ∈ centralizer (X : Set G)) :
    X ⊓ (A ⊔ B) ≤ Z := by
  rintro x ⟨hx,hxab⟩
  have hxp : x ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B hbn]
    exact hxab
  obtain ⟨y,hy,z,hz,rfl⟩ := hxp
  let y' : A := ⟨(k : G)*y*(k : G)⁻¹,
    (mem_normalizer_iff.mp (a.normalized k.property) y).mp hy⟩
  let z' : B := ⟨(k : G)*z*(k : G)⁻¹,
    (mem_normalizer_iff.mp (b.normalized k.property) z).mp hz⟩
  have he : (y' : G)*(z' : G)=y*z := by
    change (MulAut.conj (k : G)) y * (MulAut.conj (k : G)) z = y*z
    rw [← map_mul, MulAut.conj_apply, ← hX (y*z) hx]
    simp
  have heA : y⁻¹*(y' : G)=z*(z' : G)⁻¹ := by
    calc
      y⁻¹*(y' : G) = y⁻¹*((y' : G)*(z' : G))*(z' : G)⁻¹ := by group
      _ = z*(z' : G)⁻¹ := by rw [he]; group
  have heB : (z' : G)*z⁻¹=(y' : G)⁻¹*y := by
    calc
      (z' : G)*z⁻¹ = (y' : G)⁻¹*((y' : G)*(z' : G))*z⁻¹ := by group
      _ = (y' : G)⁻¹*y := by rw [he]; group
  have hyZ : y ∈ Z := by
    have hh : a.coordinates (⟨y,hy⟩⁻¹*y')=1 := by
      apply (a.coordinates_eq_one_iff _).mpr
      apply hsep
      refine ⟨A.mul_mem (A.inv_mem hy) y'.property, ?_⟩
      change y⁻¹*(y' : G) ∈ B
      rw [heA]
      exact B.mul_mem hz (B.inv_mem z'.property)
    rw [map_mul,map_inv,inv_mul_eq_one] at hh
    have hfix : specialLinearNatural 3 naturalDualSinger (a.coordinates ⟨y,hy⟩).toAdd =
        (a.coordinates ⟨y,hy⟩).toAdd := by
      rw [← hk]
      exact (a.equivariant k ⟨y,hy⟩).symm.trans (congrArg Multiplicative.toAdd hh.symm)
    exact (a.coordinates_eq_one_iff _).mp (naturalDualSinger_natural _ hfix)
  have hzZ : z ∈ Z := by
    have hh : b.coordinates (z'*(⟨z,hz⟩ : B)⁻¹)=1 := by
      apply (b.coordinates_eq_one_iff _).mpr
      apply hsep
      refine ⟨?_, B.mul_mem z'.property (B.inv_mem hz)⟩
      change (z' : G)*z⁻¹ ∈ A
      rw [heB]
      exact A.mul_mem (A.inv_mem y'.property) hy
    rw [map_mul,map_inv,mul_inv_eq_one] at hh
    have hfix : fullDual naturalDualSinger (b.coordinates ⟨z,hz⟩).toAdd =
        (b.coordinates ⟨z,hz⟩).toAdd := by
      rw [← hk]
      exact (b.equivariant k ⟨z,hz⟩).symm.trans (congrArg Multiplicative.toAdd hh)
    exact (b.coordinates_eq_one_iff _).mp (naturalDualSinger_dual _ hfix)
  exact Z.mul_mem hyZ hzZ

theorem pair_index_bound (f : N →* SL)
    (a : BinaryConjugationSection N A Z ((specialLinearNatural 3).comp f))
    (b : BinaryConjugationSection N B Z (fullDual.comp f))
    (hsep : A ⊓ B ≤ Z) (hbn : B ≤ normalizer (A : Set G))
    (k : N) (hk : f k = naturalDualSinger)
    (hX : (k : G) ∈ centralizer (X : Set G)) (hZ : Nat.card Z = 2) :
    64 ≤ X.relIndex (A ⊔ B) := by
  have hAB : A ⊓ B = Z := le_antisymm hsep (le_inf a.kernel_le b.kernel_le)
  have hAc : Nat.card A = 16 := by
    rw [a.card_section,hZ]
    norm_num [V,K,Nat.card_fun]
  have hBc : Nat.card B = 16 := by
    rw [b.card_section,hZ]
    norm_num [V,K,Nat.card_fun]
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B hbn
  rw [hAc,hBc,hAB,hZ] at hprod
  have hsup : Nat.card (A ⊔ B : Subgroup G) = 128 := by omega
  have hi := pair_fixed_intersection f a b hsep hbn k hk hX
  have hci : Nat.card (X ⊓ (A ⊔ B) : Subgroup G) ≤ 2 := by
    rw [← hZ]
    exact Nat.card_le_card_of_injective (inclusion hi) (inclusion_injective hi)
  have hcount := relIndex_mul_card_of_le (show X ⊓ (A ⊔ B) ≤ A ⊔ B from inf_le_right)
  rw [inf_relIndex_right,hsup] at hcount
  nlinarith

end Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents
