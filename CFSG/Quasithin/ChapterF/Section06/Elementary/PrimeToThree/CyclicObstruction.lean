module

public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The obstruction to a cyclic prime-to-three core

For a subgroup isomorphic to S₃, its actual two-residual is its derived
subgroup and has order three. Conjugation on a cyclic normal subgroup
has abelian image, so this residual centralizes that subgroup. If the
local S₃ supplements the cyclic normal subgroup, its residual is therefore
normal in the whole group. Coprime order counting makes it the unique
Sylow three-subgroup, and hence the unique subgroup of order three.
Two local S₃ groups must then share their cubic residual, which contradicts
the Sylow-two intersection in a Goldschmidt triple.

The preimage theorem also retains the exact A₃ preimage under a specified
quotient isomorphism. These arguments do not use F.6.9, solvable-group
recognition or the classification of Goldschmidt amalgams.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma F.6.11(2)(ii), printed pp.306–307; direct cubic-residual argument.
-/

public section

open Subgroup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.ChapterF

-- The small permutation argument is also used in
-- Theory/SpecificGroups/PSL2/TwoResidual.lean; no PSL₂ theorem is needed here.
private theorem symmetricThree_residual :
    pResidual 2 (Equiv.Perm (Fin 3)) = commutator (Equiv.Perm (Fin 3)) ∧
    Nat.card (pResidual 2 (Equiv.Perm (Fin 3))) = 3 := by
  let r : Equiv.Perm (Fin 3) := ⁅Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2⁆
  have hr : r ^ 3 = 1 := by decide +kernel
  have hrne : r ≠ 1 := by decide +kernel
  have hrmem : r ∈ commutator (Equiv.Perm (Fin 3)) :=
    commutator_mem_commutator (mem_top _) (mem_top _)
  have hcases : ∀ a b : Equiv.Perm (Fin 3),
      ⁅a,b⁆ = 1 ∨ ⁅a,b⁆ = r ∨ ⁅a,b⁆ = r ^ 2 := by decide +kernel
  have hsquares : ∀ a : Equiv.Perm (Fin 3),
      a ^ 2 = 1 ∨ a ^ 2 = r ∨ a ^ 2 = r ^ 2 := by decide +kernel
  have hR : r ∈ pResidual 2 (Equiv.Perm (Fin 3)) :=
    mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hr))
  have he : pResidual 2 (Equiv.Perm (Fin 3)) = commutator (Equiv.Perm (Fin 3)) := by
    apply le_antisymm
    · apply sInf_le
      refine ⟨inferInstance, ?_⟩
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator (Equiv.Perm (Fin 3))) q
      refine ⟨1, ?_⟩
      rw [pow_one, ← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      rcases hsquares g with h | h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact hrmem
      · rw [h]; exact pow_mem hrmem _
    · rw [commutator_def]
      apply commutator_le.mpr
      intro a _ b _
      rcases hcases a b with h | h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact hR
      · rw [h]; exact pow_mem hR _
  have hd : commutator (Equiv.Perm (Fin 3)) = zpowers r := by
    apply le_antisymm
    · rw [commutator_def]
      apply commutator_le.mpr
      intro a _ b _
      rcases hcases a b with h | h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers r
      · rw [h]; exact pow_mem (mem_zpowers r) _
    · exact zpowers_le.mpr hrmem
  refine ⟨he, ?_⟩
  rw [he, hd, Nat.card_zpowers]
  exact orderOf_eq_prime hr hrne

private theorem symmetricThree_residual_eq_alternating :
    pResidual 2 (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) := by
  have hle : pResidual 2 (Equiv.Perm (Fin 3)) ≤ alternatingGroup (Fin 3) := by
    rw [symmetricThree_residual.1, alternatingGroup_eq_sign_ker]
    exact Abelianization.commutator_subset_ker Equiv.Perm.sign
  apply eq_of_le_of_card_ge hle
  rw [symmetricThree_residual.2, nat_card_alternatingGroup, Nat.card_fin]
  decide

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem residual_of_symmetricThree (e : G ≃* Equiv.Perm (Fin 3)) :
    pResidual 2 G = commutator G ∧ Nat.card (pResidual 2 G) = 3 := by
  constructor
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_pResidual, symmetricThree_residual.1, map_commutator_eq,
      MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  · rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, map_pResidual]
    exact symmetricThree_residual.2

omit [Finite G] in
theorem symmetricThree_residual_centralizes_cyclic_normal
    (X A : Subgroup G) [X.Normal] [IsCyclic X]
    (e : A ≃* Equiv.Perm (Fin 3)) :
    (pResidual 2 A).map A.subtype ≤ centralizer (X : Set G) := by
  rw [(residual_of_symmetricThree e).1, map_subtype_commutator]
  exact (commutator_mono le_top le_top).trans
    (commutator_le_centralizer_of_isCyclic_normal X)

omit [Finite G] in
theorem symmetricThree_residual_normal_of_cyclic_supplement
    (X A : Subgroup G) [X.Normal] [IsCyclic X]
    (e : A ≃* Equiv.Perm (Fin 3)) (hgen : A ⊔ X = ⊤) :
    ((pResidual 2 A).map A.subtype).Normal := by
  have hA : A ≤ normalizer ((pResidual 2 A).map A.subtype : Set G) := by
    have hn := (pResidual 2 A).le_normalizer_map A.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn
  have hX : X ≤ normalizer ((pResidual 2 A).map A.subtype : Set G) :=
    (le_centralizer_iff.mp (symmetricThree_residual_centralizes_cyclic_normal X A e)).trans
      (centralizer_le_normalizer _)
  exact normalizer_eq_top_iff.mp (top_unique (hgen ▸ sup_le hA hX))

/-- In fact the cubic residual is the unique subgroup of order three in
the whole group, hence also in the preimage of the alternating subgroup. -/
theorem cyclic_primeToThree_supplement_unique_three
    (X A : Subgroup G) [X.Normal] [IsCyclic X]
    (hc : Nat.Coprime 3 (Nat.card X)) (eA : A ≃* Equiv.Perm (Fin 3))
    (hAX : A ⊔ X = ⊤) (hAi : A ⊓ X = ⊥)
    (D : Subgroup G) (hD : Nat.card D = 3) :
    D = (pResidual 2 A).map A.subtype := by
  let L := (pResidual 2 A).map A.subtype
  have hL : Nat.card L = 3 := by
    rw [card_map_of_injective A.subtype_injective]
    exact (residual_of_symmetricThree eA).2
  let _ : L.Normal := symmetricThree_residual_normal_of_cyclic_supplement X A eA hAX
  have hcomp : A.IsComplement' X := isComplement'_of_disjoint_and_mul_eq_univ
    (disjoint_iff.mpr hAi) (by rw [← mul_normal, hAX]; rfl)
  have hAc : Nat.card A = 6 := by
    rw [Nat.card_congr eA.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hG := hcomp.card_mul_card
  rw [hAc] at hG
  have hind := L.card_mul_index
  rw [hL, ← hG] at hind
  have hi : L.index = 2 * Nat.card X := by omega
  have hni : ¬ 3 ∣ L.index := by
    rw [hi]
    exact Nat.prime_three.coprime_iff_not_dvd.mp
      ((show Nat.Coprime 3 2 by decide).mul_right hc)
  let S : Sylow 3 G := (IsPGroup.of_card (n := 1) (by simpa using hL)).toSylow hni
  let _ : Unique (Sylow 3 G) := S.unique_of_normal (by
    simpa only [S, IsPGroup.toSylow_coe] using (inferInstance : L.Normal))
  obtain ⟨P, hP⟩ := (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hD)).exists_le_sylow
  have hle : D ≤ L := by
    have he : P = S := Subsingleton.elim _ _
    rwa [he] at hP
  exact eq_of_le_of_card_ge hle (by rw [hL, hD])

theorem cyclic_primeToThree_supplements_residual_eq
    (X A B : Subgroup G) [X.Normal] [IsCyclic X]
    (hc : Nat.Coprime 3 (Nat.card X))
    (eA : A ≃* Equiv.Perm (Fin 3)) (eB : B ≃* Equiv.Perm (Fin 3))
    (hAX : A ⊔ X = ⊤) (hAi : A ⊓ X = ⊥) :
    (pResidual 2 A).map A.subtype = (pResidual 2 B).map B.subtype := by
  apply (cyclic_primeToThree_supplement_unique_three X A hc eA hAX hAi _ ?_).symm
  rw [card_map_of_injective B.subtype_injective]
  exact (residual_of_symmetricThree eB).2

theorem cyclic_primeToThree_supplements_impossible
    {A B : Subgroup G} (h : IsGoldschmidtTriple A B)
    (X : Subgroup G) [X.Normal] [IsCyclic X]
    (hc : Nat.Coprime 3 (Nat.card X))
    (eA : A ≃* Equiv.Perm (Fin 3)) (eB : B ≃* Equiv.Perm (Fin 3))
    (hAX : A ⊔ X = ⊤) (hAi : A ⊓ X = ⊥) : False := by
  have he := cyclic_primeToThree_supplements_residual_eq X A B hc eA eB hAX hAi
  have hle : (pResidual 2 A).map A.subtype ≤ A ⊓ B :=
    le_inf (map_subtype_le _) (he ▸ map_subtype_le _)
  obtain ⟨T, hT⟩ := h.intersection_sylow
  have hp : IsPGroup 2 ((pResidual 2 A).map A.subtype) := T.isPGroup'.to_le (hT ▸ hle)
  have hcard : Nat.card ((pResidual 2 A).map A.subtype) = 3 := by
    rw [card_map_of_injective A.subtype_injective]
    exact (residual_of_symmetricThree eA).2
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hn3 : Nat.Coprime 3 (Nat.card ((pResidual 2 A).map A.subtype)) := by
    rw [hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  exact (by decide : ¬ Nat.Coprime 3 3) (by simpa only [hcard] using hn3)

/-- The actual preimage of A₃ is the product of the normal kernel and
the local cubic residual. The chosen quotient isomorphism is retained. -/
theorem alternating_preimage_eq_core_sup_residual
    (X A : Subgroup G) [X.Normal] (hAX : A ⊔ X = ⊤)
    (e : (G ⧸ X) ≃* Equiv.Perm (Fin 3)) :
    (alternatingGroup (Fin 3)).comap (e.toMonoidHom.comp (QuotientGroup.mk' X)) =
      X ⊔ (pResidual 2 A).map A.subtype := by
  let q := QuotientGroup.mk' X
  have hm : A.map q = ⊤ := by
    apply comap_injective (QuotientGroup.mk'_surjective _)
    rw [comap_map_eq, QuotientGroup.ker_mk', hAX, Subgroup.comap_top]
  have hf : Function.Surjective (q.comp A.subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype, hm]
  have hres : ((pResidual 2 A).map A.subtype).map q = pResidual 2 (G ⧸ X) := by
    rw [map_map]
    exact map_pResidual_of_surjective 2 (q.comp A.subtype) hf
  have he : (alternatingGroup (Fin 3)).comap e.toMonoidHom = pResidual 2 (G ⧸ X) := by
    rw [← symmetricThree_residual_eq_alternating, ← map_pResidual 2 e,
      comap_map_eq_self_of_injective e.injective]
  rw [← comap_comap, he, ← hres, comap_map_eq, QuotientGroup.ker_mk', sup_comm]

end CFSG.Quasithin.ChapterF
