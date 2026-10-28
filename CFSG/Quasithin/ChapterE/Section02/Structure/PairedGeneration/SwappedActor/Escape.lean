module
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormEscape
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedGeneration.SwappedActor.Centralizer
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentAutomizer
public import FeitThompson.FinalTheorem

/-!
# A norm diagonal escapes the original unique maximal subgroup

The component meets every overgroup of the chosen Sylow nontrivially. In a
proper such overgroup its intersection is proper, since the component and
Sylow generate the whole group. The norm-containment lemma makes this
intersection normal, contradicting ordinary simplicity. Perfectness and the
odd-order theorem supply evenness of the component. No solvability of the
maximal subgroup is assumed.

The literal pair centralizer joined with the original tau is therefore an
escaping E-member at the genuine automorphism two-rank bound. The paired
odd PSL₂ source applies this at degree two for attainment; no degree-one
bound is inferred.

Source: Aschbacher–Smith E.1.11, p.213, and paired E.2.2, pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.PairedGeneration.SwappedActor
variable {G : Type*} [Group G] [Finite G]

/-- A proper overgroup of the original Sylow cannot contain the norm diagonal. -/
theorem norm_not_le_proper_sylow_overgroup (T : Sylow 2 G) {K : Subgroup G}
    (hK : IsComponent G K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    {a : G} (hm : K.map (MulAut.conj a).toMonoidHom ≠ K)
    (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M) (hM : M ≠ ⊤) :
    ¬ NormPair.normRange hK hm ≤ M := by
  let := hK.2
  have heven : 2 ∣ Nat.card K := by
    by_contra hn
    have hodd : Odd (Nat.card K) := Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using hn)
    exact Group.IsPerfect.not_isSolvable K (odd_order_theorem K hodd)
  apply NormPair.norm_not_le_of_proper_nontrivial_intersection hK hm M
  · intro hb
    apply component_sylow_intersection_ne_bot T hK heven
    apply le_bot_iff.mp
    intro k hk
    have hkm : (k:G) ∈ K ⊓ M := ⟨k.property,hTM hk⟩
    rw [hb,mem_bot] at hkm
    exact mem_bot.mpr (Subtype.ext hkm)
  · intro he
    apply hM
    apply top_unique
    rw [← hgen]
    apply sup_le _ hTM
    rw [← he]
    exact inf_le_right

/-- Escape of the actual norm-tau subgroup from the original unique maximal. -/
theorem norm_tau_not_le_minimalParabolicMax
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {K A : Subgroup G} (hK : IsComponent G K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    {a : G} (hm : K.map (MulAut.conj a).toMonoidHom ≠ K) :
    ¬ NormPair.normRange hK hm ⊔ tau (T : Subgroup G) A ≤
      ChapterB.minimalParabolicMax T hP := by
  intro h
  exact norm_not_le_proper_sylow_overgroup T hK hgen hm _
    (ChapterB.minimalParabolicMax_spec T hP).2
    (ChapterB.minimalParabolicMax_spec T hP).1.ne_top (le_sup_left.trans h)

/-- The original pair centralizer and tau give an escaping E-member. -/
theorem pair_centralizer_tau_escape
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {K A : Subgroup G} (hK : IsComponent G K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (hcore : pCore 2 G = ⊥)
    (hindex : (normalizer (K : Set G)).index = 2)
    {f : ℕ} (hr : primeRank 2 (MulAut K) ≤ f)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    {a : G} (ha : a ∈ A) (hm : K.map (MulAut.conj a).toMonoidHom ≠ K)
    (hne : ¬ A ⊓ normalizer (K : Set G) ≤ centralizer (K : Set G)) :
    let I := (K ⊔ K.map (MulAut.conj a).toMonoidHom) ⊓ centralizer ({a} : Set G)
    IsEMemberAt f (T : Subgroup G) A (I ⊔ tau (T : Subgroup G) A) ∧
      ¬ I ⊔ tau (T : Subgroup G) A ≤ ChapterB.minimalParabolicMax T hP := by
  dsimp only
  rw [← NormPair.norm_eq_pair_centralizer hK hm
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha)]
  exact ⟨norm_tau_member T hK hcore hindex hr hAT ha hm hne,
    norm_tau_not_le_minimalParabolicMax T hP hK hgen hm⟩

/-- Existential form consumed by source paired generation at the automorphism rank. -/
theorem exists_member_escape
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {K A : Subgroup G} (hK : IsComponent G K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (hcore : pCore 2 G = ⊥)
    (hindex : (normalizer (K : Set G)).index = 2)
    {f : ℕ} (hr : primeRank 2 (MulAut K) ≤ f)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hmove : ¬ A ≤ normalizer (K : Set G))
    (hne : ¬ A ⊓ normalizer (K : Set G) ≤ centralizer (K : Set G)) :
    ∃ X : Subgroup G, IsEMemberAt f (T : Subgroup G) A X ∧
      ¬ X ≤ ChapterB.minimalParabolicMax T hP := by
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hmove
  have hm : K.map (MulAut.conj a).toMonoidHom ≠ K :=
    fun h => han (mem_normalizer_iff_map_conj_eq.mpr h)
  exact ⟨_,norm_tau_member T hK hcore hindex hr hAT ha hm hne,
    norm_tau_not_le_minimalParabolicMax T hP hK hgen hm⟩

end CFSG.Quasithin.ChapterE.Structure.PairedGeneration.SwappedActor
