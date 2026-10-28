module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Small indices from proper overgroups of a prime-power subgroup

If a p-subgroup P acts on cosets of a subgroup whose index is prime to p,
there is a fixed coset. Thus P lies in a conjugate of that subgroup.
If every proper overgroup of P lies in L, all proper subgroups of index less
than `[G : L]` have index divisible by p.

The overgroup premise can be certified using double cosets of a subgroup N
normalizing P: each representative lies in L or its conjugate of P generates
G together with P. This separates coverage from generation checks.

This elementary group-action argument is used for the exact ATLAS HS
point stabilizer. The source context is GLS3, Table 5.3m, printed p.274;
none of that table's structural assertions is assumed here.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

private theorem map_conj_product (P : Subgroup G) (a b : G) :
    P.map (MulAut.conj (a * b) : G →* G) =
      (P.map (MulAut.conj b : G →* G)).map (MulAut.conj a : G →* G) := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- Covering by double cosets of elements normalizing P reduces pair generation
outside L to generation at representatives. -/
theorem pairGeneration_of_normalizing_doubleCosets
    (P N L : Subgroup G) (hN : N ≤ normalizer (P : Set G)) (hNL : N ≤ L)
    {ι : Type*} (r : ι → G)
    (hcover : ∀ g : G, ∃ i a b, a ∈ N ∧ b ∈ N ∧ g = a * r i * b)
    (hrecover : ∀ i, r i ∈ L ∨ P ⊔ P.map (MulAut.conj (r i) : G →* G) = ⊤) :
    ∀ g : G, g ∉ L → P ⊔ P.map (MulAut.conj g : G →* G) = ⊤ := by
  intro g hg
  obtain ⟨i, a, b, ha, hb, rfl⟩ := hcover g
  have hr : r i ∉ L := fun hi => hg (L.mul_mem (L.mul_mem (hNL ha) hi) (hNL hb))
  have ht := (hrecover i).resolve_left hr
  have haP := mem_normalizer_iff_map_conj_eq.mp (hN ha)
  have hbP := mem_normalizer_iff_map_conj_eq.mp (hN hb)
  rw [map_conj_product, hbP, map_conj_product]
  conv_lhs => lhs; rw [← haP]
  rw [← map_sup, ht, map_top_of_surjective _ (MulAut.conj a).surjective]

/-- Generation by P and each outside conjugate forces every proper overgroup
of P into L. -/
theorem le_of_pairGeneration (P L : Subgroup G)
    (hgen : ∀ g : G, g ∉ L → P ⊔ P.map (MulAut.conj g : G →* G) = ⊤)
    (K : Subgroup G) (hK : K ≠ ⊤) (hPK : P ≤ K) : K ≤ L := by
  intro g hg
  by_contra hgl
  apply hK
  apply top_unique
  rw [← hgen g hgl]
  refine sup_le hPK ?_
  rintro x ⟨p, hp, rfl⟩
  exact K.mul_mem (K.mul_mem hg (hPK hp)) (K.inv_mem hg)

/-- A p-subgroup can be conjugated into any subgroup of index prime to p. -/
theorem exists_conjugate_overgroup_of_not_dvd_index {p : ℕ} [Fact p.Prime]
    (P K : Subgroup G) (hP : IsPGroup p P) (hi : ¬ p ∣ K.index) :
    ∃ g : G, P ≤ K.comap (MulAut.conj g : G →* G) := by
  let : MulAction P (G ⧸ K) := MulAction.compHom (G ⧸ K) P.subtype
  obtain ⟨q, hq⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ K) hi
  induction q using Quotient.inductionOn' with
  | h g =>
    refine ⟨g⁻¹, ?_⟩
    intro x hx
    have hf := (MulAction.mem_fixedPoints.mp hq ⟨x, hx⟩).symm
    change (g : G ⧸ K) = ((x * g : G) : G ⧸ K) at hf
    have hm := QuotientGroup.eq.mp hf
    simpa only [mem_comap, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv, mul_assoc] using hm

/-- A large index for the single proper overgroup of a p-subgroup excludes
small proper indices not divisible by p. Maximality is unnecessary. -/
theorem dvd_index_of_large_overgroup [Finite G] {p m : ℕ} [Fact p.Prime]
    (P L : Subgroup G) (hP : IsPGroup p P) (hlarge : m < L.index)
    (hcover : ∀ K : Subgroup G, K ≠ ⊤ → P ≤ K → K ≤ L)
    (K : Subgroup G) (hK : K ≠ ⊤) (hsmall : K.index ≤ m) : p ∣ K.index := by
  by_contra hi
  obtain ⟨g, hg⟩ := exists_conjugate_overgroup_of_not_dvd_index P K hP hi
  have hproper : K.comap (MulAut.conj g : G →* G) ≠ ⊤ := by
    intro heq
    apply hK
    apply comap_injective (f := (MulAut.conj g : G →* G)) (MulAut.conj g).surjective
    rw [heq, comap_top]
  have hbound := index_antitone (hcover _ hproper hg)
  rw [index_comap_of_surjective K (MulAut.conj g).surjective] at hbound
  exact (not_lt_of_ge (hbound.trans hsmall)) hlarge

end Subgroup
