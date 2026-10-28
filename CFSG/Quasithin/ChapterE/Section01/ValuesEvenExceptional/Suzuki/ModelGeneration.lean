module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Suzuki.ModelGeneration.SimpleGroups
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Suzuki.Geometry
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# E-generation and a predecessor obstruction for simple Suzuki groups

For any group genuinely isomorphic to `Sz(2^(2m+1))`, with `m > 0`, every
elementary subgroup of a Sylow two-subgroup lies in its first omega subgroup.
The concrete Suzuki calculation identifies this omega with the Sylow center,
of order `2^(2m+1)`. The resulting rank bound makes the whole simple group
an E-member for every nontrivial elementary subgroup. Families with no such
member have trivial weak closure and hence full weak-closure normalizer.

For the lower obstruction take all elementary subgroups of that full center
order. Inside a fixed Sylow they all equal its center, so tau is the full
Sylow. Every proper E-member therefore lies in the unique proper Sylow
overgroup. A whole-group E-member is excluded by the rank bound in its actual
two-core or solvable-radical quotient. Ovoid geometry puts the weak-closure
normalizer in the same proper Borel. Sylow conjugacy and the supplied group
isomorphism transport the concrete root and Borel calculations to the given
ambient group.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.14(1), printed p.214 (PDF p.225), citing Aschbacher,
*GF(2)-representations of finite groups* (1982), Lemma 4.7. The concrete
root calculations are Huppert--Blackburn III, XI.3.1, 3.3 and 3.6;
the unique proper Sylow overgroup is the proved Suzuki case of F.1.3(1).
These theorems supply the simple model calculation. The reduction from the
source's almost-simple group `G = F*(G) T` is a separate parent obligation.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Suzuki
variable {G : Type*} [Group G] [Finite G] {m : ℕ}

omit [Finite G] in
private theorem model_not_solvable (hm : 0 < m) (e : G ≃* SuzukiMatrixGroup m) :
    ¬ Group.IsSolvable G := by
  intro h
  let := h
  exact BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

omit [Finite G] in
private theorem elementary_le_omega (T A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ T) : A ≤ omegaOneAmbient T := by
  rw [← omegaOneAmbient_eq_self A]
  exact omegaOneAmbient_mono hAT

private theorem elementary_rank_le (hm : 0 < m) (e : G ≃* SuzukiMatrixGroup m)
    (T : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) : Group.rank A ≤ 2 * m + 1 := by
  apply IsElementaryAbelian.rank_le_of_card_le (p := 2) A
  calc
    Nat.card A ≤ Nat.card (omegaOneAmbient (T : Subgroup G)) :=
      Nat.card_le_card_of_injective
        (Subgroup.inclusion (elementary_le_omega _ _ hAT))
        (Subgroup.inclusion_injective _)
    _ = 2 ^ (2 * m + 1) := suzukiSylow_omega_card hm e T

/-- The concrete simple Suzuki model, transported along the given group
isomorphism, is E-generated at its field degree. -/
theorem model_isEGenerated (hm : 0 < m) (e : G ≃* SuzukiMatrixGroup m) :
    IsEGenerated (2 * m + 1) G := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup G := e.isSimpleGroup
  let : IsSimpleGroup (⊤ : Subgroup G) := topEquiv.isSimpleGroup
  have htop : ¬ Group.IsSolvable (⊤ : Subgroup G) := fun h =>
    model_not_solvable hm e (by
      let := h
      exact Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom) topEquiv.surjective)
  intro T
  apply ValuesEvenClassical.RankOneUpper.isEGeneratedAt_of_top_component_and_rank T
  · intro A _ _ hA
    exact ModelGeneration.eCaseComponent_of_simple _ A ⊤ htop le_top hA
  · intro A hA hAT
    let := hA
    exact elementary_rank_le hm e T A hAT

private theorem proper_overgroup_le_normalizer (e : G ≃* SuzukiMatrixGroup m)
    (T : Sylow 2 G) (K : Subgroup G) (hTK : (T : Subgroup G) ≤ K) (hK : K ≠ ⊤) :
    K ≤ normalizer (T : Set G) := by
  let P : Sylow 2 (SuzukiMatrixGroup m) := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hKP : K.map e.toMonoidHom < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro h
    apply hK
    apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
    simpa only [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using h
  have h := (ChapterF.Source.suzuki_rankOneSylowFacts m P).unique_maximal
    (K.map e.toMonoidHom) (Subgroup.map_mono hTK) hKP
  have hn : (normalizer (T : Set G)).map e.toMonoidHom =
      normalizer (P : Set (SuzukiMatrixGroup m)) :=
    Subgroup.map_normalizer_eq_of_bijective _ e.bijective
  rw [← hn] at h
  exact (Subgroup.map_le_map_iff_of_injective e.injective).mp h

private theorem tau_omega (hm : 0 < m) (e : G ≃* SuzukiMatrixGroup m)
    (T : Sylow 2 G) : tau (T : Subgroup G) (omegaOneAmbient (T : Subgroup G)) = T := by
  apply le_antisymm (tau_le _ _)
  intro x hx
  apply mem_centralizerModulo_iff.mpr
  refine ⟨hx, ?_⟩
  intro a ha
  rw [suzukiSylow_omega_eq_center hm e T] at ha
  obtain ⟨z, hz, rfl⟩ := ha
  have hc : (z : G) * x = x * z := congrArg Subtype.val
    ((mem_center_iff.mp hz (⟨x, hx⟩ : T)).symm)
  change ⁅(z : G), x⁆ ∈ pCore 2 G
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
  exact Subgroup.one_mem _

private theorem omega_ne_bot (hm : 0 < m) (e : G ≃* SuzukiMatrixGroup m)
    (T : Sylow 2 G) : omegaOneAmbient (T : Subgroup G) ≠ ⊥ := by
  intro h
  have hc := suzukiSylow_omega_card hm e T
  have hc1 : Nat.card (omegaOneAmbient (T : Subgroup G)) = 1 := by rw [h]; simp
  rw [hc1] at hc
  have hp : 1 < 2 ^ (2 * m + 1) := one_lt_pow₀ (by decide) (by omega)
  omega

private theorem omega_normalizer_le (hm : 0 < m) (e : G ≃* SuzukiMatrixGroup m)
    (T : Sylow 2 G) :
    normalizer (omegaOneAmbient (T : Subgroup G) : Set G) ≤ normalizer (T : Set G) := by
  obtain ⟨f, hT, hB⟩ := suzukiSylow_aligned_equiv hm e T
  have hroot : omegaOneAmbient (SuzukiRootSubgroup m) ≠ ⊥ := by
    intro h
    have h' : omegaOneAmbient (T : Subgroup G) = ⊥ := by
      rw [← hT, ← map_omegaOneAmbient_injective f.toMonoidHom f.injective,
        h, Subgroup.map_bot]
    exact omega_ne_bot hm e T h'
  have h := suzuki_normalizer_le_borel_of_le_root m hm
    (omegaOneAmbient (SuzukiRootSubgroup m)) hroot (omegaOneAmbient_le _)
  have hh := Subgroup.map_mono (f := f.toMonoidHom) h
  rw [Subgroup.map_equiv_normalizer_eq,
    map_omegaOneAmbient_injective f.toMonoidHom f.injective, hT, hB] at hh
  exact hh

private theorem sylow_normalizer_ne_top (hm : 0 < m) (e : G ≃* SuzukiMatrixGroup m)
    (T : Sylow 2 G) : normalizer (T : Set G) ≠ ⊤ := by
  obtain ⟨f, _, hB⟩ := suzukiSylow_aligned_equiv hm e T
  intro h
  apply suzukiBorelSubgroup_ne_top m hm
  apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
  rw [hB, h, Subgroup.map_top_of_surjective f.toMonoidHom f.surjective]

/-- At the preceding rank, elementary subgroups of the full center order
have weak-closure normalizer and all E-members confined to one proper Borel.
The family is defined intrinsically in G and is invariant under conjugation. -/
theorem model_predecessor_obstruction (hm : 0 < m) (e : G ≃* SuzukiMatrixGroup m) :
    ∃ (T : Sylow 2 G) (Ω : Set (Subgroup G)), IsElementaryFamily Ω ∧
      ∃ M : Subgroup G, M ≠ ⊤ ∧
        normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M ∧
        ∀ A ∈ Ω, A ≤ (T : Subgroup G) → ∀ K : Subgroup G,
          IsEMemberAt (2 * m + 1 - 1) (T : Subgroup G) A K → K ≤ M := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup G := e.isSimpleGroup
  let T : Sylow 2 G := Classical.choice inferInstance
  let Z := omegaOneAmbient (T : Subgroup G)
  let : IsElementaryAbelian 2 Z := suzukiSylow_omega_elementary hm e T
  let Ω : Set (Subgroup G) := {A | IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ (2 * m + 1)}
  have hΩ : IsElementaryFamily Ω := by
    refine ⟨fun A hA => hA.1, ?_⟩
    intro g A hA
    let := hA.1
    exact ⟨IsElementaryAbelian.map _, (Subgroup.card_map_of_injective
      (MulAut.conj g).injective).trans hA.2⟩
  have hZΩ : Z ∈ Ω := ⟨inferInstance, suzukiSylow_omega_card hm e T⟩
  have hAZ : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A = Z := by
    intro A hA hAT
    let := hA.1
    apply Subgroup.eq_of_le_of_card_ge (elementary_le_omega _ _ hAT)
    exact le_of_eq ((suzukiSylow_omega_card hm e T).trans hA.2.symm)
  have hW : weakClosure (T : Subgroup G) Ω = Z := by
    apply le_antisymm
    · exact sSup_le (fun A hA => (hAZ A hA.1 hA.2).le)
    · exact le_sSup ⟨hZΩ, omegaOneAmbient_le _⟩
  refine ⟨T, Ω, hΩ, normalizer (T : Set G), sylow_normalizer_ne_top hm e T, ?_, ?_⟩
  · rw [hW]
    exact omega_normalizer_le hm e T
  · intro A hA hAT K hK
    have hTK : (T : Subgroup G) ≤ K := by
      have h := hK.1.2.2.2.1
      rw [hAZ A hA hAT, tau_omega hm e T] at h
      exact h.trans inf_le_right
    apply proper_overgroup_le_normalizer e T K hTK
    intro htop
    subst K
    have hr := ModelGeneration.rank_le_of_top_member (model_not_solvable hm e) hK
    let := hA.1
    have hl := IsElementaryAbelian.rank_ge_of_card hA.2
    omega
end CFSG.Quasithin.ChapterE.ExceptionalValues.Suzuki
