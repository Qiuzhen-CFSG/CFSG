module
public import Theory.Mathieu.M23.QuasithinGeometry.ElementarySylow
/-!
# Exhaustive elementary containers in the native 128-element Sylow

The two existing E16 groups and four explicit E8 groups contain every
elementary subgroup of this Sylow. For an involution outside the E16 groups,
the certified list of its commuting involutions is the union of two E8 groups.
The union-of-two-subgroups lemma gives containment in one of them. Otherwise
the same argument applies to the two E16 groups. No normality is assumed.

This is the finite subgroup-placement calculation used for the M22 image in
Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Lemma 2.2.1, pp.489--490.
`Native` transports it through the literal M22 embedding; normalizers of the
E8 containers require further geometry. The permutation enumeration and its
ATLAS source attribution are reused from `M23Geometry.Involutions.Fusion`.
The additional XOR products and union witnesses are checked by Lean's kernel.
-/

public noncomputable section
open Sporadic.Mathieu
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
open M23Geometry FusionCertificate ElementarySylow
@[expose] def smallIndex : Fin 4 → Fin 8 → Fin 128 :=
  ![![0, 1, 5, 7, 50, 51, 52, 54], ![0, 1, 16, 17, 34, 35, 50, 51], ![0, 7, 51, 52, 75, 76, 120, 127], ![0, 16, 35, 51, 75, 107, 88, 120]]
private theorem products0 : ∀ (i j : Fin 8) (x : Fin 23),
    pointTable (smallIndex 0 i) (pointTable (smallIndex 0 j) x) =
      pointTable (smallIndex 0 (i ^^^ j)) x := by decide +kernel

private theorem products1 : ∀ (i j : Fin 8) (x : Fin 23),
    pointTable (smallIndex 1 i) (pointTable (smallIndex 1 j) x) =
      pointTable (smallIndex 1 (i ^^^ j)) x := by decide +kernel

private theorem products2 : ∀ (i j : Fin 8) (x : Fin 23),
    pointTable (smallIndex 2 i) (pointTable (smallIndex 2 j) x) =
      pointTable (smallIndex 2 (i ^^^ j)) x := by decide +kernel

private theorem products3 : ∀ (i j : Fin 8) (x : Fin 23),
    pointTable (smallIndex 3 i) (pointTable (smallIndex 3 j) x) =
      pointTable (smallIndex 3 (i ^^^ j)) x := by decide +kernel

private theorem products (k : Fin 4) (i j : Fin 8) :
    perm (smallIndex k i) * perm (smallIndex k j) = perm (smallIndex k (i ^^^ j)) := by
  apply Equiv.ext
  intro x
  fin_cases k
  · exact products0 i j x
  · exact products1 i j x
  · exact products2 i j x
  · exact products3 i j x

/-- Multiplication of the literal E8 permutation rows is binary XOR. -/
theorem smallIndex_mul (k : Fin 4) (i j : Fin 8) :
    perm (smallIndex k i) * perm (smallIndex k j) = perm (smallIndex k (i ^^^ j)) :=
  products k i j

private theorem initialIndex (k : Fin 4) : smallIndex k 0 = 0 := by fin_cases k <;> rfl
private theorem index_injective : ∀ k, Function.Injective (smallIndex k) := by decide +kernel
private theorem square (k : Fin 4) (i : Fin 8) :
    perm (smallIndex k i) * perm (smallIndex k i) = 1 := by
  rw [products, show i ^^^ i = 0 by simp, initialIndex, initial]

@[expose] def rawSmall (k : Fin 4) : Subgroup (Equiv.Perm (Fin 23)) where
  carrier := Set.range (fun i => perm (smallIndex k i))
  one_mem' := ⟨0, by
    change perm (smallIndex k 0) = 1
    rw [initialIndex, initial]⟩
  mul_mem' := by
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    exact ⟨i ^^^ j,(products k i j).symm⟩
  inv_mem' := by
    rintro _ ⟨i,rfl⟩
    exact ⟨i,eq_inv_iff_mul_eq_one.mpr (square k i)⟩

@[expose] def small (k : Fin 4) : Subgroup M23 := (rawSmall k).subgroupOf M23

theorem small_le_sylow (k : Fin 4) : small k ≤ subgroup := by
  rintro x ⟨i,hi⟩
  change x.val ∈ rawSubgroup
  change perm (smallIndex k i) = x.val at hi
  rw [← hi]
  exact perm_mem _

theorem small_card (k : Fin 4) : Nat.card (small k) = 8 := by
  let f : Fin 8 → small k := fun i =>
    ⟨⟨perm (smallIndex k i),rawSubgroup_le (perm_mem _)⟩,⟨i,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact index_injective k (perm_injective
        (congrArg (fun x : small k => (x.val : Equiv.Perm (Fin 23))) h))
    · rintro ⟨g,i,hi⟩
      exact ⟨i,Subtype.ext (Subtype.ext hi)⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf).symm).trans (Nat.card_fin 8)

theorem small_elementary (k : Fin 4) : IsElementaryAbelian 2 (small k) := by
  refine { is_comm := ⟨?_⟩, exponent_dvd_p := ?_ }
  · rintro ⟨x,i,hi⟩ ⟨y,j,hj⟩
    apply Subtype.ext
    apply Subtype.ext
    change perm (smallIndex k i) = x.val at hi
    change perm (smallIndex k j) = y.val at hj
    change x.val * y.val = y.val * x.val
    rw [← hi,← hj,products,products,Fin.xor_comm]
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨x,i,hi⟩
    apply Subtype.ext
    apply Subtype.ext
    change perm (smallIndex k i) = x.val at hi
    change x.val ^ 2 = 1
    rw [← hi,pow_two]
    exact square k i

@[expose] def pairChoice : Fin 8 → Fin 2 → Fin 4 :=
  ![![0, 1], ![0, 2], ![1, 3], ![1, 3], ![0, 1], ![0, 2], ![2, 3], ![2, 3]]

private theorem commuting_cover : ∀ (k : Fin 8) (j : Fin 12),
    ∃ (b : Fin 2) (i : Fin 8), commutingIndex k j = smallIndex (pairChoice k b) i := by
  decide +kernel

/-- All elementary subgroups of the enumerated Sylow lie in the two native
E16 groups or one of four native E8 groups. No normality is assumed. -/
theorem elementary_sylow_cover (A : Subgroup M23) [IsElementaryAbelian 2 A]
    (hAS : A ≤ subgroup) :
    (∃ b : Fin 2, A ≤ candidate b) ∨ ∃ k : Fin 4, A ≤ small k := by
  have square_index (a : A) (i : Fin 128) (hi : perm i = a.val.val) :
      ∀ x, pointTable i (pointTable i x) = x := by
    have he := congrArg (fun z : M23 => z.val)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) a.val a.property)
    rw [pow_two] at he
    change a.val.val * a.val.val = 1 at he
    rw [← hi] at he
    exact fun x => Equiv.congr_fun he x
  by_cases hex : ∃ (k : Fin 8) (a : A), a.val.val = perm (exceptionalIndex k)
  · obtain ⟨k,a,ha⟩ := hex
    have hcover : (A : Set M23) ⊆ (small (pairChoice k 0) : Set M23) ∪
        small (pairChoice k 1) := by
      intro x hx
      obtain ⟨i,hi⟩ := exists_perm ⟨x.val,hAS hx⟩
      have hc : ∀ z, pointTable (exceptionalIndex k) (pointTable i z) =
          pointTable i (pointTable (exceptionalIndex k) z) := by
        have he := congrArg (fun u : A => u.val.val) (mul_comm a ⟨x,hx⟩)
        change a.val.val * x.val = x.val * a.val.val at he
        rw [ha,← hi] at he
        exact fun z => Equiv.congr_fun he z
      obtain ⟨j,rfl⟩ := exceptional_commuting k i (square_index ⟨x,hx⟩ i hi) hc
      obtain ⟨b,l,hl⟩ := commuting_cover k j
      fin_cases b
      · exact Or.inl ⟨l,(congrArg perm hl).symm.trans hi⟩
      · exact Or.inr ⟨l,(congrArg perm hl).symm.trans hi⟩
    rcases SubgroupClass.subset_union.mp hcover with h | h
    · exact Or.inr ⟨pairChoice k 0,h⟩
    · exact Or.inr ⟨pairChoice k 1,h⟩
  · have hcover : (A : Set M23) ⊆ (candidate 0 : Set M23) ∪ candidate 1 := by
      intro x hx
      obtain ⟨i,hi⟩ := exists_perm ⟨x.val,hAS hx⟩
      rcases square_cases i (square_index ⟨x,hx⟩ i hi) with ⟨b,j,rfl⟩ | ⟨k,rfl⟩
      · fin_cases b
        · exact Or.inl ⟨j,hi⟩
        · exact Or.inr ⟨j,hi⟩
      · exact (hex ⟨k,⟨x,hx⟩,hi.symm⟩).elim
    rcases SubgroupClass.subset_union.mp hcover with h | h
    · exact Or.inl ⟨0,h⟩
    · exact Or.inl ⟨1,h⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
