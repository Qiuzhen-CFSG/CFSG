module

public import Stellmacher.Recognition.LyonsU3Four.Basic
public import Theory.PPrimeCore

/-!
# The actual Sylow normalizer and its automizer index

The numerical automizer is the index of S C_G(S) in N_G(S), as in the
proof of Lyons's Lemma 1, pp. 372–373. The supplied Sylow subgroup maps
canonically and injectively into the quotient of its normalizer by its odd
core: an element in the kernel has order dividing both 64 and an odd number.
This map fixes the compatibility convention for the later semidirect product.
-/

namespace Stellmacher.Recognition.LyonsU3Four

/-- The order of the automizer N_G(S)/(S C_G(S)). -/
@[expose] public noncomputable def automizerIndex {G : Type*} [Group G]
    (S : Sylow 2 G) : ℕ :=
  ((S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G)).relIndex
    (Subgroup.normalizer (S : Set G))

/-- The canonical map of the supplied Sylow into the actual odd-core quotient. -/
@[expose] public def sylowNormalizerQuotientMap {G : Type*} [Group G] (S : Sylow 2 G) :
    S →* (Subgroup.normalizer (S : Set G) ⧸
      pPrimeCore 2 (Subgroup.normalizer (S : Set G))) :=
  (QuotientGroup.mk' (pPrimeCore 2 (Subgroup.normalizer (S : Set G)))).comp
    (Subgroup.inclusion (S : Subgroup G).le_normalizer)

public theorem sylowNormalizerQuotientMap_injective
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (h : SylowStructure S) :
    Function.Injective (sylowNormalizerQuotientMap S) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply (sylowNormalizerQuotientMap S).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro s hs
  change s = 1
  let n : Subgroup.normalizer (S : Set G) :=
    Subgroup.inclusion (S : Subgroup G).le_normalizer s
  have hn : n ∈ pPrimeCore 2 (Subgroup.normalizer (S : Set G)) :=
    (QuotientGroup.eq_one_iff n).mp hs
  have hdodd := (pPrimeCore 2 (Subgroup.normalizer (S : Set G))).orderOf_dvd_natCard hn
  have horder : orderOf n = orderOf s := by
    rw [← Subgroup.orderOf_coe n, ← Subgroup.orderOf_coe s]
    rfl
  rw [horder] at hdodd
  have hdtwo : orderOf s ∣ 64 := h.card ▸ orderOf_dvd_natCard s
  have hcop : Nat.Coprime 64
      (Nat.card (pPrimeCore 2 (Subgroup.normalizer (S : Set G)))) :=
    (pPrimeCore_coprime_card (p := 2)).pow_left 6
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdtwo hdodd)

end Stellmacher.Recognition.LyonsU3Four
