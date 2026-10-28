module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Tightly embedded subgroups

A tightly embedded subgroup has even order and odd intersection with each
distinct conjugate. A nontrivial 2-subgroup lying in it therefore determines
its conjugate uniquely: a second such conjugate would have an intersection
whose order is both odd and divisible by the order of the 2-subgroup.
Consequently normalizers of nontrivial 2-subgroups normalize the tightly
embedded subgroup.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, definition in I.7 and Lemma I.7.2(5), pp. 425--426.
-/

namespace Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- A subgroup of even order whose intersection with every distinct conjugate
has odd order. Conjugation here sends `x` to `g * x * g⁻¹`. -/
@[expose] public def IsTightlyEmbedded (K : Subgroup G) : Prop :=
  Even (Nat.card K) ∧ ∀ g : G, g ∉ Subgroup.normalizer (K : Set G) →
    Odd (Nat.card ↥(K ⊓ K.map (MulAut.conj g).toMonoidHom))

/-- The normalizer of a nontrivial 2-subgroup of a tightly embedded subgroup
normalizes the latter. This is the ambient normalizer assertion of I.7.2(5). -/
public theorem IsTightlyEmbedded.normalizer_le {K Q : Subgroup G}
    (hK : IsTightlyEmbedded K) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) (hle : Q ≤ K) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  by_contra hgK
  have hodd := hK.2 g hgK
  have hconj : Q ≤ K.map (MulAut.conj g).toMonoidHom := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hg]
    exact Subgroup.map_mono hle
  have hQcap : Q ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom := le_inf hle hconj
  obtain ⟨n, hcard⟩ := IsPGroup.iff_card.mp hQ
  have hcop : (Nat.card Q).Coprime
      (Nat.card ↥(K ⊓ K.map (MulAut.conj g).toMonoidHom)) := by
    rw [hcard]
    exact hodd.coprime_two_left.pow_left n
  have hbot := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  rw [inf_eq_left.mpr hQcap] at hbot
  exact hne hbot

end Theory.GroupTheory
