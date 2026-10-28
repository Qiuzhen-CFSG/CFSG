module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Local
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.AlternatingFive
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Centralizer

/-!
# The conditional L₂ Borel exclusion, 15.3.30

The marked Borel constructs R ∈ Syl₂(LR), for R = O₂(Y₊S), and the
minimal-parabolic geometry of both LR and I. Apply C.1.26 to I, whose
Sylow subgroup is the S controlled by 15.3.29. Its residual central
product has the selected component L as a factor, giving the L₂ and
A₅ block alternatives. The actual M ∩ L-invariant four-group in
U(L)/C_U(L) excludes the A₅ module. The natural L₂ block calculation
then gives C_S(Y₊) ≤ C_G(L), including the central covering layers.
Thus V₁ centralizes L, and L ≤ C_G(V₁) ≤ N_G(V₁) ≤ M is impossible.

`excluded_of_earlier` uses the precise conclusions of 15.3.29 directly.
`lemma_15_3_30` instead derives them through the earlier implications
15.3.11(3),(12), constructing I = LS and the required nontrivial action.
Both results retain the genuine local SQTK hypothesis, its catalogue,
the universal C.1.26 implication with distinguished characteristic
subgroups, and the preceding local conclusions as explicit inputs.
The parent recognition theorem must discharge these inputs and provide
the marked alternative 15.3.28(1); this is a conditional exclusion, not
an unconditional classification of the star quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.30, printed pp.1131–1132.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}

/-- Exclude the marked L₂ branch using the earlier conclusions 15.3.11(2),
15.3.26(1), and 15.3.29. The block alternatives and centralizer containment
are proved in this application; neither is an input. -/
theorem excluded_of_earlier
    (choices : PushingUp.DistinguishedPairs.{u})
    (source : PushingUp.C126Source 𝒦 choices)
    (d : LocalData G) {I : Subgroup G} {c : ComponentWitness d I}
    (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (hSQTK : IsSQTK 𝒦 I) (h : Earlier d I c)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]
    (b : BorelIdentification d I c n F)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (hres : d.Yplus = (primeToResidual 3 (d.MI I)).map (d.MI I).subtype)
    (hpush : ∀ A : Subgroup d.S, A.Characteristic → A ≠ ⊥ →
      ¬ ((A.map d.S.subtype).subgroupOf I).Normal)
    (hnorm : normalizer (d.V₁ : Set G) ≤ d.M)
    (hVY : d.V₁ ≤ centralizer (d.Yplus : Set G)) : False := by
  obtain ⟨⟨_, hblocks⟩, _⟩ :=
    PushingUp.local_block_recognition choices source d hI hf hSQTK h P hP b hc hpush
  rcases hblocks with ⟨m, hblock⟩ | hblock
  · have hVL : d.V₁ ≤ centralizer (c.L : Set G) :=
      (le_inf (plane_one_le_sylow d) hVY).trans
        (sylow_centralizer_yplus_le_component b h P hP hblock hres)
    exact c.outside ((le_centralizer_iff.mp hVL).trans
      ((Subgroup.centralizer_le_normalizer _).trans hnorm))
  · exact AlternatingFive.not_isAlternatingBlock b h P hP hblock

/-- Conditional 15.3.30 with the actual even-parameter projective model and
marked Borel of 15.3.28(1). In addition to `Earlier`, the preceding inputs
are the three-rank bound from 15.3.7, the kernel containment 15.3.11(2),
the residual identity 15.3.26(1), and the implications 15.3.11(3),(12).
The standing solvable-invariant control is retained in this source-facing
interface; its uses occur in the preceding conclusions supplied by `Earlier`.
The full universal C.1.26 theorem and local SQTK hypothesis remain explicit. -/
theorem lemma_15_3_30
    (choices : PushingUp.DistinguishedPairs.{u})
    (source : PushingUp.C126Source 𝒦 choices)
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (hSQTK : IsSQTK 𝒦 I) (hRank : primeRank 3 d.Yplus = 1)
    (_hcontrol : SolvableInvariantControl d I) (h : Earlier d I c)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hYRank : 2 ≤ primeRank 3 d.Y)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (hres : d.Yplus = (primeToResidual 3 (d.MI I)).map (d.MI I).subtype)
    (h11_3 : (Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M ∧
        d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G))) →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ I) ∧
        normalizer (d.V₁ : Set G) ≤ d.M)
    (h11_12 : ∀ J : Subgroup G, J ≤ I →
      ⁅d.V, Stellmacher.twoResidualAmbient (d.Y ⊓ J)⁆ ≠ ⊥ → ¬ J ≤ d.M →
      ∀ A : Subgroup d.S, A.Characteristic → A ≠ ⊥ →
        ¬ ((A.map d.S.subtype).subgroupOf (J ⊔ d.S)).Normal)
    {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]
    (b : BorelIdentification d I c n F) : False := by
  have hYM : d.Yplus ≤ d.M := (h.theta_eq ▸ theta_le (d.MI I)).trans inf_le_left
  have hgen := (lemma_15_3_27_4_of_containment d hI c P hP h.contains hYM).1
  have hVact : ⁅d.V, d.Yplus⁆ ≠ ⊥ := by
    rw [h.plane_eq]
    exact (Subgroup.nontrivial_iff_ne_bot _).mp
      (Finite.one_lt_card_iff_nontrivial.mp (by
        have hcard : Nat.card d.V₂ = 4 := d.action.card_plane _
        rw [hcard]
        decide))
  obtain ⟨hpush, hnorm, hVY⟩ := lemma_15_3_29_of_containment d c hRank hYRank
    h.contains hgen hVact h11_3 h11_12
  exact excluded_of_earlier choices source d hI hf hSQTK h P hP b hc hres
    hpush hnorm hVY

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

end
