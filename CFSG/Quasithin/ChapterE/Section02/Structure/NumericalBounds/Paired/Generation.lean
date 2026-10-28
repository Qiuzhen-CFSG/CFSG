module

public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.MaximalSolvable
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.NormalizedActor
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedGeneration.SwappedActor
public import Theory.SpecificGroups.Suzuki.TwoRank
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly

/-!
# E-generation for actual paired binary rank-one components

The unique Sylow maximal is solvable. A nontrivial family either has full
weak-closure normalizer or contains an actor noncentral on the chosen factor.
A normalized actor supplies its component-tau member; a swapping actor
supplies the genuine fixed diagonal, except when its stabilizer is trivial,
where the full rank-one orbit is itself an E-member. Each member is
nonsolvable and hence escapes the original maximal subgroup.

The sharp automorphism two-ranks discharge every rank premise for binary
PSL₂ and Suzuki. No generic actor-transfer assertion is used.
Source: Aschbacher–Smith E.1.11 and E.2.2, printed pp.213–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired
variable {G : Type*} [Group G] [Finite G]

theorem isEGenerated_of_noncentral_members {f : ℕ}
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    [Group.IsSolvable (ChapterB.minimalParabolicMax T hP)]
    (K : Subgroup G) (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (hmembers : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ (T : Subgroup G) →
      ¬ A ≤ centralizer (K : Set G) →
      ∃ X : Subgroup G, IsEMemberAt f (T : Subgroup G) A X ∧ ¬ Group.IsSolvable X) :
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
    refine ⟨A,hA,hAT,X,hX,?_⟩
    intro hXM
    exact hns (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hXM) (inclusion_injective hXM))

omit [Finite G] in
private theorem component_tau_not_solvable (T A : Subgroup G) {K : Subgroup G}
    (hK : IsComponent G K) [IsSimpleGroup K] :
    ¬ Group.IsSolvable (K ⊔ tau T A : Subgroup G) := by
  let : IsQuasisimple K := hK.2
  intro hs
  let := hs
  exact Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show K ≤ K ⊔ tau T A from le_sup_left)) (inclusion_injective _))

theorem coreFree_isEGenerated_of_rank {f : ℕ} (hf : 0 < f)
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    [Group.IsSolvable (ChapterB.minimalParabolicMax T hP)]
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
  apply isEGenerated_of_noncentral_members T hP K hgen
  intro A hA hAT hAC
  let := hA
  by_cases hAN : A ≤ normalizer (K : Set G)
  · exact ⟨_,normalized_actor_member T hK hgen hrad hl hi hr hAT hAN hAC,
      component_tau_not_solvable _ _ hK⟩
  · by_cases hfix : A ⊓ normalizer (K : Set G) ≤ centralizer (K : Set G)
    · have hra := rank_one_of_moved_pair_and_fixed_stabilizer T hK hgen hl hcore hi hAT hAN hfix
      have hAt : A ≤ tau (T : Subgroup G) A := le_sup_left.trans (sup_pCore_le_tau T A hAT)
      have ho := moved_pair_orbit_eq_residual T hK hgen hl hi
        (show ¬ tau (T : Subgroup G) A ≤ normalizer (K : Set G) from fun h => hAN (hAt.trans h))
      exact ⟨_,ChiefOrbit.tau_join_member_of_full_orbit T hK hrad hl hAT ho
        (.inr ⟨hAN,hra⟩) (by omega),component_tau_not_solvable _ _ hK⟩
    · exact PairedGeneration.SwappedActor.exists_nonsolvable_member T hK hcore hi hr hAT hAN hfix

theorem coreFree_linear_isEGenerated
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup G) (hK : IsComponent G K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hn : ¬ K.Normal)
    {f : ℕ} (hf : 2 ≤ f) (hm : ClassicalGroup.IsPSL K 2 (2^f)) :
    IsEGenerated f G := by
  have hrad : solvableRadical G = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup K := isSimpleGroup_of_isQuasisimple_of_solvableRadical_eq_bot hrad hK.1
  let : Group.IsSolvable (ChapterB.minimalParabolicMax T hP) :=
    rankOne_maximal_solvable hG T hP K hK hgen hn (.linear f (by omega) hm)
  apply coreFree_isEGenerated_of_rank (by omega) hG T hP hs hJ K hK hgen hn
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  rw [primeRank_equiv 2 (MulAut.congr e)]
  exact Theory.PSL2.BinaryAutomorphismRank.psl2_automorphism_two_rank_le hf hF

theorem coreFree_suzuki_isEGenerated
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup G) (hK : IsComponent G K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hn : ¬ K.Normal)
    {m : ℕ} (hm : 0 < m) (e : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    IsEGenerated (2*m+1) G := by
  have hrad : solvableRadical G = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup K := isSimpleGroup_of_isQuasisimple_of_solvableRadical_eq_bot hrad hK.1
  let : Group.IsSolvable (ChapterB.minimalParabolicMax T hP) :=
    rankOne_maximal_solvable hG T hP K hK hgen hn (.suzuki m ⟨e⟩)
  apply coreFree_isEGenerated_of_rank (by omega) hG T hP hs hJ K hK hgen hn
  rw [primeRank_equiv 2 (MulAut.congr e)]
  exact BenderSuzuki.MatrixGroups.suzuki_automorphism_two_rank m hm

end CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired
