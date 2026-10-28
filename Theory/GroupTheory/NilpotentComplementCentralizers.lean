module

public import Theory.GroupTheory.Commutator.NilpotentAB
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Prime cores of centralizers in nilpotent-by-p groups

For a normal nilpotent p-complement X, the p-core of C_G(U) equals O_p(G)
for every U ≤ X. Its local p-core centralizes C_X(U), since the two normal
subgroups there have coprime orders. The nilpotent A × B lemma then makes
it centralize X. The full centralizer C_G(X) is nilpotent: its map to the
p-group G/X has central kernel. Its Sylow p-subgroup is therefore normal
in G, putting the local core inside O_p(G). The reverse inclusion follows
from coprimeness and relative normality.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, G.8.3,
printed p.349, combined manuscript of 1 March 2004. This proof works for
any prime and proves the assertion without the cited external theorem.
-/

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

private theorem normal_coprime_core_centralizes (p : ℕ) [Fact p.Prime]
    (X : Subgroup G) [X.Normal] (hcop : Nat.Coprime p (Nat.card X)) :
    pCore p G ≤ centralizer (X : Set G) := by
  have hcop' : Nat.Coprime (Nat.card (pCore p G)) (Nat.card X) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := G)).exists_card_eq
    rw [hn]
    exact hcop.pow_left n
  exact commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_disjoint (disjoint_of_coprime_natCard hcop'))

private theorem prime_subgroup_le_core_of_normal_nilpotent
    (p : ℕ) [Fact p.Prime] (N Q : Subgroup G) [N.Normal]
    (hN : Group.IsNilpotent N) (hQ : IsPGroup p Q) (hQN : Q ≤ N) :
    Q ≤ pCore p G := by
  have hQNp : IsPGroup p (Q.subgroupOf N) := hQ.comap_subtype
  obtain ⟨S, hS⟩ := hQNp.exists_le_sylow
  have hm := map_mono (f := N.subtype) hS
  rw [map_subgroupOf_eq_of_le hQN] at hm
  exact hm.trans (S.map_le_pCore inferInstance hN p)

/-- Centralizers of subgroups of a nilpotent normal p-complement have
exactly the ambient p-core. -/
public theorem pCoreIn_centralizer_eq_of_nilpotent_normal_complement
    (p : ℕ) [Fact p.Prime] (X U : Subgroup G) [X.Normal]
    (hX : Group.IsNilpotent X) (hcop : Nat.Coprime p (Nat.card X))
    (hquot : IsPGroup p (G ⧸ X)) (hUX : U ≤ X) :
    (centralizer (U : Set G)).pCoreIn p = pCore p G := by
  let C := centralizer (U : Set G)
  let R := C.pCoreIn p
  have hRC : R ≤ C := pCoreIn_le p C
  have hRp : IsPGroup p R := isPGroup_pCoreIn p C
  have hcopR : Nat.Coprime (Nat.card R) (Nat.card X) := by
    obtain ⟨n, hn⟩ := hRp.exists_card_eq
    rw [hn]
    exact hcop.pow_left n
  have hdis : R ⊓ X = ⊥ := (disjoint_of_coprime_natCard hcopR).eq_bot
  have hCR : C ≤ normalizer (R : Set G) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore p C))
  have hcomm : ⁅X ⊓ C, R⁆ = ⊥ := by
    apply bot_unique
    rw [← hdis]
    exact le_inf (le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hCR))
      ((commutator_mono inf_le_left le_rfl).trans (commutator_le_left X R))
  have hUR : ⁅U, R⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hRC
  have hXR : ⁅X, R⁆ = ⊥ := nilpotent_a_times_b_centralizer X X U R hX le_rfl hUX
    (hUX.trans X.le_normalizer) le_normalizer_of_normal hUR hcopR
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hRCX : R ≤ centralizer (X : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]
  have hnilC : Group.IsNilpotent (centralizer (X : Set G)) := by
    let f := (QuotientGroup.mk' X).comp (centralizer (X : Set G)).subtype
    have hker : f.ker ≤ center (centralizer (X : Set G)) := by
      intro x hx
      have hxX : (x : G) ∈ X := (QuotientGroup.eq_one_iff _).mp hx
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext ((y.property x hxX).symm)
    let : Group.IsNilpotent (G ⧸ X) := hquot.isNilpotent
    exact isNilpotent_of_ker_le_center f hker
  apply le_antisymm
  · exact prime_subgroup_le_core_of_normal_nilpotent p _ R hnilC hRp hRCX
  · apply le_pCoreIn_of_normalizes pCore_isPGroup
    · exact (normal_coprime_core_centralizes p X hcop).trans (centralizer_le hUX)
    · exact le_normalizer_of_normal

end Subgroup
