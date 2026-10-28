module

public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.Generation
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedGeneration.SwappedActor.Escape
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
/-!
# Positive E-generation for the actual two-factor source configuration

The norm diagonal escapes the original maximal subgroup by simplicity of
the component intersection, without a solvability hypothesis on the maximal.
The actual actor alternatives therefore give generation at every positive
bound on the component automorphism two-rank. Its finite rank supplies a
positive witness without choosing a source model. Prime-field PSL₂ gives
an explicit bound of two; no degree-one claim is made here.

This is only the genuine paired minimal-parabolic case, not a general
E.1.11 transfer. Source: Aschbacher–Smith E.1.11 and E.2.2, pp.213–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired
variable {G : Type*} [Group G] [Finite G]

theorem isEGenerated_of_noncentral_escape {f : ℕ}
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup G) (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (hmembers : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ (T : Subgroup G) →
      ¬ A ≤ centralizer (K : Set G) →
      ∃ X : Subgroup G, IsEMemberAt f (T : Subgroup G) A X ∧ ¬ X ≤ ChapterB.minimalParabolicMax T hP) :
    IsEGenerated f G := by
  apply IsEGeneratedAt.isEGenerated (T := T)
  let M := ChapterB.minimalParabolicMax T hP
  have hm := ChapterB.minimalParabolicMax_spec T hP
  apply ValuesEvenClassical.RankOneUpper.isEGeneratedAt_of_borel_escape T M
  · intro H hTH hH
    exact hP.1.le_maximal ⟨hm.2,hm.1.covBy_top⟩ hTH (lt_top_iff_ne_top.mpr hH)
  · intro Ω hΩ hNW
    have hex : ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧
        ¬ A ≤ centralizer (K : Set G) := by
      by_contra h
      push Not at h
      have hWC : weakClosure (T : Subgroup G) Ω ≤ centralizer (K : Set G) :=
        sSup_le fun A hA => h A hA.1 hA.2
      have hKM : K ≤ M := (le_centralizer_iff.mp hWC).trans
        ((Subgroup.centralizer_le_normalizer _).trans hNW)
      exact hm.1.ne_top (top_unique (hgen ▸ sup_le hKM hm.2))
    obtain ⟨A,hA,hAT,hAC⟩ := hex
    obtain ⟨X,hX,hns⟩ := hmembers A (hΩ.1 A hA) hAT hAC
    exact ⟨A,hA,hAT,X,hX,hns⟩

theorem coreFree_isEGenerated_of_aut_rank {f : ℕ} (hf : 0 < f)
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup G) (hK : IsComponent G K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hn : ¬ K.Normal)
    (hr : primeRank 2 (MulAut K) ≤ f) : IsEGenerated f G := by
  have hrad : solvableRadical G = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  have hcore := SimpleSocle.pCore_eq_bot hrad 2
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup K := isSimpleGroup_of_isQuasisimple_of_solvableRadical_eq_bot hrad hK.1
  have hi : (normalizer (K : Set G)).index = 2 := by
    rcases component_normal_or_pair hG T hK hgen with h | ⟨t,_,_,_,_,_,_,hi⟩
    · exact (hn h.1).elim
    · exact hi
  have hl := residual_eq_layer T hK hgen
  have hKM : ¬ K ≤ ChapterB.minimalParabolicMax T hP := by
    intro h
    exact (ChapterB.minimalParabolicMax_spec T hP).1.ne_top
      (top_unique (hgen ▸ sup_le h (ChapterB.minimalParabolicMax_spec T hP).2))
  apply isEGenerated_of_noncentral_escape T hP K hgen
  intro A hA hAT hAC
  let := hA
  by_cases hAN : A ≤ normalizer (K : Set G)
  · exact ⟨_,normalized_actor_member T hK hgen hrad hl hi hr hAT hAN hAC,
      fun hx => hKM (le_sup_left.trans hx)⟩
  · by_cases hfix : A ⊓ normalizer (K : Set G) ≤ centralizer (K : Set G)
    · have hra := rank_one_of_moved_pair_and_fixed_stabilizer T hK hgen hl hcore hi hAT hAN hfix
      have hAt : A ≤ tau (T : Subgroup G) A := le_sup_left.trans (sup_pCore_le_tau T A hAT)
      have ho := moved_pair_orbit_eq_residual T hK hgen hl hi
        (show ¬ tau (T : Subgroup G) A ≤ normalizer (K : Set G) from fun h => hAN (hAt.trans h))
      exact ⟨_,ChiefOrbit.tau_join_member_of_full_orbit T hK hrad hl hAT ho
        (.inr ⟨hAN,hra⟩) (by omega),fun hx => hKM (le_sup_left.trans hx)⟩
    · exact PairedGeneration.SwappedActor.exists_member_escape T hP hK hgen hcore hi hr hAT hAN hfix


theorem coreFree_prime_linear_isEGenerated_two
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup G) (hK : IsComponent G K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hn : ¬ K.Normal)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hm : ClassicalGroup.IsPSL K 2 p) :
    IsEGenerated 2 G := by
  apply coreFree_isEGenerated_of_aut_rank (by decide) hG T hP hs hJ K hK hgen hn
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [primeRank_equiv 2 (MulAut.congr e)]
  exact Theory.PSL2.prime_card_automorphism_two_rank F hF hp

theorem coreFree_exists_isEGenerated
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup G) (hK : IsComponent G K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hn : ¬ K.Normal) :
    ∃ f : ℕ, 0 < f ∧ IsEGenerated f G :=
  ⟨max 1 (primeRank 2 (MulAut K)), by omega,
    coreFree_isEGenerated_of_aut_rank (by omega) hG T hP hs hJ K hK hgen hn (le_max_right _ _)⟩

end CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired
