module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeSingleFactor
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeSingleFusion
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Factorization.SolvableThreePrime
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Thompson factorization excludes the singleton five-factor branch

Fusion places Ω₁(T) inside the seed core whenever it lies in R₁. Thompson
heredity then makes LT normalize J₀(T) and Ω₁(Z(J₁(T))). Both are nontrivial
two-groups, so uniqueness over LT places their full normalizers in M.

For the original normal escaping lift Y with five-group quotient by O₂(Y),
YT is solvable of order prime to three. Characteristic two passes from the
original local I to this Sylow overgroup. Solvable Thompson factorization
gives its literal ordered product of the two normalizers, forcing Y into M
and contradicting its original escape. The quotient kernel is never erased.
LargePrimeSingleFactorSource applies this to the original canonical family.

Source: Aschbacher–Smith, 14.7.6, printed p.1045; GLS Number 2, G.26.18(a),
printed pp.152–153; refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Stellmacher ChapterB
open Chapter12.Section08
open scoped IsMulCommutative Pointwise
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

include F in
private theorem seed_rank_lower
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    3 ≤ twoRank (T : Subgroup G) := by
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty (T : Subgroup G)
  have hc := hA.2.2 V h.chosen.le_sylow h.chosen.elementary
  have hV : Nat.card V = 2 ^ 3 := by simpa only [F.last] using F.card 3 (by decide)
  rw [hV,elementaryAbelianMaxSubgroups_card_eq _ _ hA,maxOrder_eq_two_pow_rank] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

private theorem thompson_nonzero (R : Subgroup G) {j : ℕ} (hj : j < twoRank R) :
    thompsonJ R j ≠ ⊥ := by
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty R
  have hAJ : A ≤ thompsonJ R 0 := by
    rw [thompsonJ_zero]
    exact le_sSup hA
  have hc : 1 < Nat.card A := by
    rw [elementaryAbelianMaxSubgroups_card_eq R A hA,maxOrder_eq_two_pow_rank]
    exact one_lt_pow₀ (by decide : 1 < 2) (by omega)
  intro he
  have hAbot : A = ⊥ := bot_unique
    ((hAJ.trans (lemma_B_2_3_1 R (Nat.zero_le j) hj)).trans he.le)
  rw [hAbot,Subgroup.card_bot] at hc
  omega

private theorem omega_center_nonzero (R : Subgroup G)
    (hR : IsPGroup 2 R) (hne : R ≠ ⊥) : omegaOneCenterAmbient R ≠ ⊥ := by
  have hi := Chapter1.RadicalNormalizers.omegaCenterIn_ne_bot R hR hne
  intro he
  apply hi
  apply Subgroup.map_injective (f := R.subtype) R.subtype_injective
  simpa [omegaOneCenterAmbient,Chapter1.RadicalNormalizers.omegaCenterIn] using he

/-- Uniqueness over the original LT controls the two full normalizers
used by solvable Thompson factorization. -/
theorem thompson_normalizers_le_of_omega_le_point_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hΩ : omegaOneAmbient (T : Subgroup G) ≤ F.Ri L 1) :
    normalizer (thompsonJ (T : Subgroup G) 0 : Set G) ≤ normalizer (L : Set G) ∧
      normalizer (omegaOneCenterAmbient (thompsonJ (T : Subgroup G) 1) : Set G) ≤
        normalizer (L : Set G) := by
  have hr := seed_rank_lower (F := F) h
  have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  have huniq (M : Subgroup G) (hM : IsMaximalTwoLocal M)
      (hLM : L ⊔ (T : Subgroup G) ≤ M) : M = normalizer (L : Set G) :=
    Set.mem_singleton_iff.mp ((h.maximal_unique structural hu).2 ▸
      show M ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ L ⊔ (T : Subgroup G) ≤ M} from
        ⟨hM,hLM⟩)
  have hJp (j : ℕ) : IsPGroup 2 (thompsonJ (T : Subgroup G) j) :=
    T.isPGroup'.to_le (thompsonJ_le _ _)
  have hn (j : ℕ) (hj : j < twoRank (T : Subgroup G)) :
      L ⊔ (T : Subgroup G) ≤ normalizer (thompsonJ (T : Subgroup G) j : Set G) :=
    (thompson_normalized_of_omega_le_point_core h structural hΩ j hj).2
  refine ⟨normalizer_le_of_unique_maximalTwoLocal huniq (hJp 0)
    (thompson_nonzero _ (by omega)) (hn 0 (by omega)),?_⟩
  apply normalizer_le_of_unique_maximalTwoLocal huniq
    ((hJp 1).to_le (by intro x hx; exact ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1))
    (omega_center_nonzero _ (hJp 1) (thompson_nonzero _ (by omega)))
  apply (hn 1 (by omega)).trans
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  change (omegaOneCenterAmbient (thompsonJ (T : Subgroup G) 1)).map
    (MulAut.conj g).toMonoidHom = _
  change (thompsonJ (T : Subgroup G) 1).map (MulAut.conj g).toMonoidHom =
    thompsonJ (T : Subgroup G) 1 at hg
  rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,hg]

/-- A solvable subgroup containing T inside the original local I lies in M
when its order is prime to three and all involutions of T lie in R₁. -/
theorem local_threePrime_le_normalizer_of_omega
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hΩ : omegaOneAmbient (T : Subgroup G) ≤ F.Ri L 1)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (W : Subgroup G) (hTW : (T : Subgroup G) ≤ W) (hWI : W ≤ I)
    [Group.IsSolvable W] (h3 : Nat.Coprime 3 (Nat.card W)) :
    W ≤ normalizer (L : Set G) := by
  let S : Sylow 2 W := T.subtype hTW
  have hS : (S : Subgroup W).map W.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTW
  have hr : 1 < twoRank (S : Subgroup W) := by
    rw [←twoRank_map_injective W.subtype W.subtype_injective,hS]
    exact lt_of_lt_of_le (by decide : 1 < 3) (seed_rank_lower (F := F) h)
  have hchar := F.localKernel_characteristicTwo h.source.simpleQTKE L _ I hI
  have hfit := generalizedFitting_eq_pCore_of_sylow_overgroup T W I hTW hWI hchar
  have hc : centralizer (pCore 2 W : Set W) ≤ pCore 2 W := by
    rw [←hfit]
    exact centralizer_generalizedFitting_le W
  have hf := solvable_threePrime_thompson_factorization S hr h3 hc
  have hp := thompson_factorization_subgroup_product W (S : Subgroup W) hf
  rw [hS] at hp
  obtain ⟨hN0,hN1⟩ := thompson_normalizers_le_of_omega_le_point_core h structural hΩ
  intro x hx
  have hh : x ∈ ((W ⊓ normalizer (thompsonJ (T : Subgroup G) 0 : Set G) : Subgroup G) : Set G) *
      ((W ⊓ normalizer (omegaOneCenterAmbient (thompsonJ (T : Subgroup G) 1) : Set G) : Subgroup G) : Set G) := hp ▸ hx
  obtain ⟨a,ha,b,hb,rfl⟩ := hh
  exact (normalizer (L : Set G)).mul_mem (hN0 ha.2) (hN1 hb.2)

/-- The original normal five-core lift prevents Ω₁(T) from lying in R₁.
Its full two-core is retained when proving the order of YT is prime to three. -/
theorem local_five_lift_not_omega_le_point_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    [Group.IsSolvable I] (Y : Subgroup I) [Y.Normal]
    (hY5 : IsPGroup 5 (Y ⧸ pCore 2 Y))
    (hout : ¬ Y.map I.subtype ≤ normalizer (L : Set G)) :
    ¬ omegaOneAmbient (T : Subgroup G) ≤ F.Ri L 1 := by
  intro hΩ
  let N := Y.map I.subtype
  let W := N ⊔ (T : Subgroup G)
  have hTI : (T : Subgroup G) ≤ I := fun _ ht => hI.1.2 (Or.inr ht)
  have hWI : W ≤ I := sup_le (map_subtype_le Y) hTI
  let : Group.IsSolvable W := Group.isSolvable_of_isSolvable_injective (f := inclusion hWI) (inclusion_injective hWI)
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) := by
    apply hTI.trans
    have hh := Y.le_normalizer_map I.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hY3 : Nat.Coprime 3 (Nat.card Y) := by
    obtain ⟨a,ha⟩ := hY5.exists_card_eq
    obtain ⟨b,hb⟩ := (show IsPGroup 2 (pCore 2 Y) from pCore_isPGroup).exists_card_eq
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 Y),ha,hb]
    exact ((by decide : Nat.Coprime 3 5).pow_right a).mul_right
      ((by decide : Nat.Coprime 3 2).pow_right b)
  have hN3 : Nat.Coprime 3 (Nat.card N) := by
    rw [card_map_of_injective I.subtype_injective]
    exact hY3
  have hT3 : Nat.Coprime 3 (Nat.card (T : Subgroup G)) := by
    obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have h3 : Nat.Coprime 3 (Nat.card W) := by
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes N (T : Subgroup G) hTN
    apply (hN3.mul_right hT3).of_dvd_right
    rw [hc]
    exact dvd_mul_left _ _
  exact hout (le_sup_left.trans
    (local_threePrime_le_normalizer_of_omega h structural hΩ I hI W le_sup_right hWI h3))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
