module

public import Theory.GroupAction.AbelianCoprimeFullFixedGeneration
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.ElementaryAbelian.Basic
public import Theory.PPrimeCore

/-!
# Centralizing an odd core from four-group local cores

Let V be an elementary four-subgroup of a finite subgroup I. If V lies in
the two-core of the ambient centralizer of every nonidentity element of V,
then V centralizes the ambient image of O(I).

For each v, the commutator of V with C_{O(I)}(v) lies in both O(I) and
O₂(C_G(v)), and is therefore trivial. Coprime fixed-point generation for
the conjugation action of V then makes V centralize the whole odd core.

Source: the odd-core step of Aschbacher–Smith, *The Classification of
Quasithin Groups*, 14.6.7(3), combined manuscript of 1 March 2004.
-/

namespace Subgroup
open scoped IsMulCommutative

/-- An elementary four contained in every relevant centralizer two-core
centralizes the odd core of each subgroup containing it. -/
public theorem pPrimeCore_map_le_centralizer_of_four_local_cores
    {G : Type*} [Group G] [Finite G]
    (I V : Subgroup G) [IsElementaryAbelian 2 V]
    (hcard : Nat.card V = 4) (hVI : V ≤ I)
    (hlocal : ∀ v ∈ V, v ≠ 1 → V ≤ (centralizer ({v} : Set G)).pCoreIn 2) :
    (pPrimeCore 2 I).map I.subtype ≤ centralizer (V : Set G) := by
  let D := (pPrimeCore 2 I).map I.subtype
  have hIN : I ≤ normalizer (D : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pPrimeCore 2 I).le_normalizer_map I.subtype
  have hcop : Nat.Coprime 2 (Nat.card D) := by
    rw [show Nat.card D = Nat.card (pPrimeCore 2 I) from
      card_map_of_injective I.subtype_injective]
    exact pPrimeCore_coprime_card
  have hfixed (v : G) (hv : v ∈ V) (hne : v ≠ 1) :
      D ⊓ centralizer ({v} : Set G) ≤ centralizer (V : Set G) := by
    let C := centralizer ({v} : Set G)
    let R := C.pCoreIn 2
    have hCN : C ≤ normalizer (R : Set G) := by
      change C ≤ normalizer ((pCore 2 C).map C.subtype : Set G)
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
        (pCore 2 C).le_normalizer_map C.subtype
    have hdisj : D ⊓ R = ⊥ := by
      obtain ⟨n, hn⟩ := (isPGroup_pCoreIn 2 C).exists_card_eq
      exact (disjoint_of_coprime_natCard (by
        rw [hn]; exact hcop.symm.pow_right n)).eq_bot
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    rw [← hdisj]
    apply le_inf
    · exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hVI.trans hIN))
    · rw [commutator_comm]
      exact (commutator_mono (hlocal v hv hne) le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hCN))
  let _ : Fact (IsPGroup 2 V) := ⟨IsElementaryAbelian.isPGroup 2 V⟩
  let _ : MulDistribMulAction V D :=
    conjMulDistribMulActionOfLeNormalizer V D (hVI.trans hIN)
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup_action
    (G := D) (A := V) 2 hcop
  have htop : (⊤ : Subgroup D) ≤ (centralizer (V : Set G)).comap D.subtype := by
    rw [← hgen]
    refine iSup₂_le fun Y hY => ?_
    have hYne : Y ≠ ⊥ := by
      intro he
      subst Y
      let _ : IsCyclic (V ⧸ (⊥ : Subgroup V)) := hY
      exact (IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) hcard)
        (isCyclic_of_surjective (QuotientGroup.quotientBot (G := V))
          QuotientGroup.quotientBot.surjective)
    obtain ⟨v, hvY, hvne⟩ := Y.bot_or_exists_ne_one.resolve_left hYne
    intro d hd
    apply hfixed v v.property (fun he => hvne (Subtype.ext he))
    refine ⟨d.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have he := congrArg Subtype.val (hd (⟨v, hvY⟩ : Y))
    change (v : G) * (d : G) * (v : G)⁻¹ = (d : G) at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  intro d hd
  exact htop (mem_top (⟨d, hd⟩ : D))

end Subgroup
