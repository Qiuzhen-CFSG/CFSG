module

public import Theory.Mathieu.M23.QuasithinGeometry.ElementarySylow.Involutions

/-!
# Two concrete elementary abelian subgroups of native M23

The checked XOR product tables define actual subgroups inside the native
Sylow group. Their sixteen distinct permutations give their orders, and
the symmetric multiplication and diagonal tables prove elementary abelianity.
Source: Aschbacher–Smith H.14.2(1), printed p.397.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry.ElementarySylow
open FusionCertificate

/-- The two concrete elementary subgroups in the certified Sylow group. -/
def rawCandidate (b : Fin 2) : Subgroup (Equiv.Perm (Fin 23)) where
  carrier := Set.range (fun i => perm (candidateIndex b i))
  one_mem' := ⟨0, by
    change perm (candidateIndex b 0) = 1
    rw [candidate_initial, initial]⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨productIndex b i j, (product_correct b i j).symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i, (eq_inv_iff_mul_eq_one.mpr (candidate_sq b i))⟩

theorem rawCandidate_le (b : Fin 2) : rawCandidate b ≤ rawSubgroup := by
  rintro _ ⟨i, rfl⟩
  exact perm_mem _

noncomputable def candidate (b : Fin 2) : Subgroup M23 := (rawCandidate b).subgroupOf M23

theorem mem_candidate (b : Fin 2) (g : M23) :
    g ∈ candidate b ↔ ∃ i, perm (candidateIndex b i) = (g : Equiv.Perm (Fin 23)) := Iff.rfl

theorem candidate_le_sylow (b : Fin 2) : candidate b ≤ subgroup := by
  intro g hg
  exact rawCandidate_le b hg

theorem candidate_card (b : Fin 2) : Nat.card (candidate b) = 16 := by
  let f : Fin 16 → candidate b := fun i =>
    ⟨⟨perm (candidateIndex b i), rawSubgroup_le (perm_mem _)⟩, ⟨i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact candidate_injective b (perm_injective
        (congrArg (fun x : candidate b => (x.val : Equiv.Perm (Fin 23))) h))
    · rintro ⟨g, i, hi⟩
      exact ⟨i, Subtype.ext (Subtype.ext hi)⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf).symm).trans (Nat.card_fin 16)

theorem candidate_elementary (b : Fin 2) : IsElementaryAbelian 2 (candidate b) := by
  refine { is_comm := ⟨?_⟩, exponent_dvd_p := ?_ }
  · intro x y
    obtain ⟨i,hi⟩ := (mem_candidate b x.val).mp x.property
    obtain ⟨j,hj⟩ := (mem_candidate b y.val).mp y.property
    apply Subtype.ext
    apply Subtype.ext
    change x.val.val * y.val.val = y.val.val * x.val.val
    rw [← hi, ← hj]
    exact (product_correct b i j).trans ((congrArg (fun k => perm (candidateIndex b k))
      (product_symmetric b i j)).trans (product_correct b j i).symm)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    obtain ⟨i,hi⟩ := (mem_candidate b x.val).mp x.property
    apply Subtype.ext
    apply Subtype.ext
    change x.val.val ^ 2 = 1
    rw [← hi, pow_two]
    exact candidate_sq b i

end Sporadic.Mathieu.M23Geometry.ElementarySylow
