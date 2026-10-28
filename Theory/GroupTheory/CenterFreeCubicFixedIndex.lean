module
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# Fixed indices in centerless cubic local groups

Let H/O₂(H) be S₃ and Z(H)=1. Two distinct Sylow two-subgroups generate H.
For a normal subgroup V, its fixed subgroups under those Sylows are conjugate
and have trivial intersection. The subgroup index inequality therefore bounds
|V| by the square of its Sylow fixed index. A subgroup crossing O₂(H) inside
a Sylow has the same fixed subgroup on V whenever O₂(H) centralizes V.

This elementary cubic specialization replaces the ambient commutator-center
step in Stellmacher (9.2), Journal of Algebra 190 (1997), p.48, when the
local S₃ quotient is already known, as in Aschbacher–Smith F.6.5.
-/

public section
open Subgroup
namespace SymmetricThreeTwoCore
variable {H : Type*} [Group H] [Finite H]

private theorem sylow_sup_conj_eq_top
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) (S : Sylow 2 H)
    (g : H) (hg : g ∉ (S : Subgroup H)) :
    (S : Subgroup H) ⊔ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = ⊤ := by
  let S' := (S : Subgroup H).map (MulAut.conj g).toMonoidHom
  have hi := sylow_index_three e S
  have hdiv := index_dvd_of_le (show (S : Subgroup H) ≤ (S : Subgroup H) ⊔ S' from le_sup_left)
  rw [hi] at hdiv
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
  · exact index_eq_one.mp h1
  · have he : (S : Subgroup H) ⊔ S' = S := by
      by_contra hne
      have hlt := index_strictAnti (lt_of_le_of_ne
        (show (S : Subgroup H) ≤ (S : Subgroup H) ⊔ S' from le_sup_left) (Ne.symm hne))
      omega
    have hle : S' ≤ (S : Subgroup H) := he ▸ le_sup_right
    have heq : S' = (S : Subgroup H) := eq_of_le_of_card_ge hle (by
      rw [show Nat.card S' = Nat.card S from card_map_of_injective (MulAut.conj g).injective])
    apply (hg ?_).elim
    rw [← sylow_self_normalizing e S]
    exact mem_normalizer_iff_map_conj_eq.mpr heq

/-- A center-free cubic local group has at most the square of the Sylow fixed index
on any normal subgroup. -/
theorem normal_card_le_fixed_index_sq
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) (S : Sylow 2 H)
    (V : Subgroup H) [V.Normal] (hcenter : center H = ⊥) :
    Nat.card V ≤ ((V ⊓ centralizer (S : Set H)).relIndex V)^2 := by
  classical
  have hSne : (S : Subgroup H) ≠ ⊤ := by
    intro he
    have hi := sylow_index_three e S
    rw [he, index_top] at hi
    omega
  obtain ⟨g,hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hSne)
  let f := (MulAut.conj g).toMonoidHom
  let C := V ⊓ centralizer (S : Set H)
  let D := C.map f
  have hV : V.map f = V := mem_normalizer_iff_map_conj_eq.mp (by
    rw [V.normalizer_eq_top]
    trivial)
  have hDV : D ≤ V := (map_mono (show C ≤ V from inf_le_left)).trans_eq hV
  have hDindex : D.relIndex V = C.relIndex V := by
    change (C.map f).relIndex V = _
    calc
      (C.map f).relIndex V = (C.map f).relIndex (V.map f) := by rw [hV]
      _ = C.relIndex V := relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  have hCD : C ⊓ D = ⊥ := by
    apply le_bot_iff.mp
    rintro x ⟨hx, y,hy,hxy⟩
    have hs : (S : Subgroup H) ⊔ (S : Subgroup H).map f ≤ centralizer ({x} : Set H) := by
      apply sup_le
      · intro z hz
        rw [mem_centralizer_singleton_iff]
        exact hx.2 z hz
      · rintro _ ⟨z,hz,rfl⟩
        rw [mem_centralizer_singleton_iff, ← hxy]
        simpa only [← map_mul] using congrArg f (hy.2 z hz)
    rw [sylow_sup_conj_eq_top e S g hg.2] at hs
    have hc : x ∈ center H := mem_center_iff.mpr (fun z =>
      mem_centralizer_singleton_iff.mp (hs (mem_top z)))
    exact hcenter ▸ hc
  have hh := index_inf_le (H := C.subgroupOf V) (K := D.subgroupOf V)
  have he : C.subgroupOf V ⊓ D.subgroupOf V = ⊥ := by
    ext x
    change (x.val ∈ C ∧ x.val ∈ D) ↔ x = 1
    rw [← mem_inf, hCD]
    change x.val = (1 : V).val ↔ x = 1
    exact Subtype.val_injective.eq_iff
  rw [he, index_bot] at hh
  change Nat.card V ≤ C.relIndex V * D.relIndex V at hh
  rw [hDindex] at hh
  simpa only [pow_two] using hh

/-- A nontrivial Sylow image with fixed index two bounds a normal subgroup by four. -/
theorem normal_card_le_four_of_fixed_index_two
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) (S : Sylow 2 H)
    (V : Subgroup H) [V.Normal] (hcenter : center H = ⊥)
    (hVQ : V ≤ centralizer (pCore 2 H : Set H))
    (U : Subgroup H) (hUS : U ≤ (S : Subgroup H))
    (hUnot : ¬ U ≤ pCore 2 H)
    (hfixed : (V ⊓ centralizer (U : Set H)).relIndex V = 2) : Nat.card V ≤ 4 := by
  have hQS : pCore 2 H ≤ (S : Subgroup H) := pCore_isPGroup.le_sylow_of_normal S
  have hQi : (pCore 2 H).relIndex (S : Subgroup H) = 2 := by
    have hh := relIndex_mul_index hQS
    rw [core_index e, sylow_index_three e S] at hh
    omega
  have hgen : pCore 2 H ⊔ U = (S : Subgroup H) := by
    have hle : pCore 2 H ⊔ U ≤ (S : Subgroup H) := sup_le hQS hUS
    have hh := relIndex_mul_relIndex (pCore 2 H) (pCore 2 H ⊔ U)
      (S : Subgroup H) le_sup_left hle
    rw [hQi] at hh
    rcases Nat.prime_mul_iff.mp (hh ▸ Nat.prime_two) with ⟨_, h1⟩ | ⟨_,h1⟩
    · exact le_antisymm hle (relIndex_eq_one.mp h1)
    · exact (hUnot (le_sup_right.trans (relIndex_eq_one.mp h1))).elim
  have hfix : V ⊓ centralizer (S : Set H) = V ⊓ centralizer (U : Set H) := by
    apply le_antisymm (inf_le_inf_left _ (centralizer_le hUS))
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hs : pCore 2 H ⊔ U ≤ centralizer ({x} : Set H) := by
      apply sup_le
      · intro q hq
        exact mem_centralizer_singleton_iff.mpr (hVQ hx.1 q hq)
      · intro y hy
        exact mem_centralizer_singleton_iff.mpr (hx.2 y hy)
    rw [hgen] at hs
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hs hy)
  have hh := normal_card_le_fixed_index_sq e S V hcenter
  rw [hfix,hfixed] at hh
  exact hh

end SymmetricThreeTwoCore
