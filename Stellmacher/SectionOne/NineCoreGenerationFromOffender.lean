module

public import Stellmacher.SectionOne.LemmaOneSeven
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalFixedIndex
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Canonical generation from a nontrivial offender over a nine-core

Suppose the order-nine odd core and a Sylow two-subgroup generate the
ambient group, and the Sylow has a unique maximal overgroup. A nontrivial
canonical offender then forces its normal closure to supplement the Sylow.

The odd-core splitting in (1.7)(a) is the key. The odd centralizer of the
canonical product cannot supplement the Sylow: cardinality would make it
the entire odd core, contradicting the elementary offender's faithful
conjugation action on that core. If the canonical product also failed to
supplement the Sylow, both proper joins would lie in the unique maximal overgroup, which
would then contain the whole odd core and the Sylow.

The representation-theoretic existence of an offender remains a separate
input. This is the group-theoretic step toward Stellmacher (9.1)(8), printed
p.47, PDF page 37 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionOne

universe u

private theorem le_unique_maximal_nineCore
    {K : Type u} [Group K] [Finite K]
    {R L : Subgroup K} {M : Subgroup (⊤ : Subgroup K)}
    (hunique : ∀ M' : Subgroup (⊤ : Subgroup K), IsCoatom M' →
      R ≤ M'.map (⊤ : Subgroup K).subtype → M' = M)
    (hRL : R ≤ L) (hL : L ≠ ⊤) :
    L ≤ M.map (⊤ : Subgroup K).subtype := by
  have hproper : L.subgroupOf (⊤ : Subgroup K) ≠ ⊤ := by
    intro htop
    apply hL
    rw [← Subgroup.map_subgroupOf_eq_of_le
      (show L ≤ (⊤ : Subgroup K) from le_top), htop,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨maximal, hmaximal, hLmaximal⟩ :=
    (eq_top_or_exists_le_coatom (L.subgroupOf (⊤ : Subgroup K))).resolve_left hproper
  have hRmaximal : R ≤ maximal.map (⊤ : Subgroup K).subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le
      (show L ≤ (⊤ : Subgroup K) from le_top)] at hRL
    exact hRL.trans (Subgroup.map_mono hLmaximal)
  rw [← hunique maximal hmaximal hRmaximal]
  rw [← Subgroup.map_subgroupOf_eq_of_le
    (show L ≤ (⊤ : Subgroup K) from le_top)]
  exact Subgroup.map_mono hLmaximal

public theorem nineCore_canonical_generation_of_oneJ_ne_bot
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (R : Sylow 2 K)
    (hgen : oddCore K ⊔ (R : Subgroup K) = ⊤)
    (hunique : IsUniqueMaximalContaining (R : Subgroup K) ⊤)
    (hoddcard : Nat.card (oddCore K) = 9)
    (hJ : oneJ (V := V) (R : Subgroup K) ≠ ⊥) :
    oneE (V := V) (R : Subgroup K) ⊔ (R : Subgroup K) = ⊤ := by
  let W := oddCore K
  let E := oneE (V := V) (R : Subgroup K)
  let J := oneJ (V := V) (R : Subgroup K)
  let C := W ⊓ Subgroup.centralizer (E : Set K)
  let _ : W.Normal := pPrimeCore_normal
  let _ : E.Normal := Subgroup.normalClosure_normal
  let _ : C.Normal := inferInstance
  have hWp : IsPGroup 3 W := IsPGroup.of_card (p := 3) (n := 2) hoddcard
  have hWR : Disjoint W (R : Subgroup K) :=
    IsPGroup.disjoint_of_ne 3 2 (by decide) W R hWp R.isPGroup'
  have hCR : Disjoint C (R : Subgroup K) := hWR.mono inf_le_left le_rfl
  have hKcard : Nat.card W * Nat.card R = Nat.card K := by
    have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes W
      (R : Subgroup K) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    rw [hWR.eq_bot, hgen, Subgroup.card_bot,
      Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K).toEquiv,
      one_mul] at hcard
    exact hcard
  have hstructure := lemma_one_seven h R hJ
  have hJE : J ≤ E := Subgroup.subset_normalClosure
  have hCproper : C ⊔ (R : Subgroup K) ≠ ⊤ := by
    intro htop
    have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes C
      (R : Subgroup K) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    rw [hCR.eq_bot, htop, Subgroup.card_bot,
      Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K).toEquiv,
      one_mul, ← hKcard] at hcard
    have hCW : C = W := Subgroup.eq_of_le_of_card_ge inf_le_left
      (Nat.mul_right_cancel (Nat.card_pos (α := R)) hcard).ge
    have hWcent : W ≤ Subgroup.centralizer (E : Set K) :=
      hCW ▸ (show C ≤ Subgroup.centralizer (E : Set K) from inf_le_right)
    have hJcent : J ≤ Subgroup.centralizer (W : Set K) := by
      intro actor hactor
      rw [Subgroup.mem_centralizer_iff]
      intro element helement
      exact (Subgroup.mem_centralizer_iff.mp (hWcent helement)
        actor (hJE hactor)).symm
    have hcentral := RankOneThreeGroupAssembly.sylow_inf_centralizer_oddCore_eq_bot
      h J hstructure.part_b.2.2.1 hWp
    apply hJ
    exact le_antisymm ((le_inf le_rfl hJcent).trans hcentral.le) bot_le
  by_contra hEproper
  obtain ⟨maximal, hmaximal, hRmaximal, huniq⟩ := hunique
  have hEmaximal : E ≤ maximal.map (⊤ : Subgroup K).subtype :=
    le_sup_left.trans (le_unique_maximal_nineCore huniq le_sup_right hEproper)
  have hCmaximal : C ≤ maximal.map (⊤ : Subgroup K).subtype :=
    le_sup_left.trans (le_unique_maximal_nineCore huniq le_sup_right hCproper)
  have hWmaximal : W ≤ maximal.map (⊤ : Subgroup K).subtype := by
    change oddCore K ≤ _
    rw [hstructure.part_a.1]
    apply iSup_le
    intro index
    fin_cases index
    · exact (Subgroup.map_subtype_le _).trans hEmaximal
    · exact hCmaximal
  have htop : (⊤ : Subgroup K) ≤ maximal.map (⊤ : Subgroup K).subtype := by
    calc
      (⊤ : Subgroup K) = W ⊔ (R : Subgroup K) := hgen.symm
      _ ≤ maximal.map (⊤ : Subgroup K).subtype := sup_le hWmaximal hRmaximal
  apply hmaximal.1
  apply Subgroup.map_subtype_inj.mp
  apply le_antisymm (Subgroup.map_mono le_top)
  simpa [← MonoidHom.range_eq_map, Subgroup.range_subtype] using htop


end Stellmacher.SectionOne
