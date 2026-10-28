module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal.Source
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.CentralizerSupplement

/-!
# Normalizer uniqueness at C_T(U) in original 13.1.14

For the literal U=[R₂(N_G(L)),L], construct L₁=N_L(C_T(U))^∞. The
centralizer Frattini theorem proves L₁∈L(G,T) and L=O∞(L)L₁, with the
actual solvable residual and subgroup inclusions. Hence the permitted
13.1.9 supplement-uniqueness premise controls every maximal two-local
overgroup of N_G(C_T(U)). Its nonempty family is exactly {N_G(L)}.

The final theorem applies this uniqueness to the existing weak-closure
consumer on the same U. TI and the multiple-overgroup hypothesis are used
there; the normalizer uniqueness itself does not require them. Original
13.1.9 remains the sole explicit earlier-source premise, owned separately
by the supplement argument. No normalizer or supplement-existence callback
is introduced.

Source: Aschbacher--Smith, 13.1.9 and 13.1.14, printed pp.869--871 and
875--876. Final 13.1.7 assembly remains in the terminal source development.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal
open Chapter1 Chapter1.Section02 Chapter12.Section02 Chapter1.RadicalNormalizers
variable {G : Type*} [Group G] [Finite G]

/-- The actual Frattini supplement for R=C_T([R₂(N_G(L)),L]) is the
solvable residual N_L(R)^∞. It belongs to L(G,T) and supplements O∞(L). -/
theorem normalizerMoved_frattini_supplement
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    normalizerResidual L ((T : Subgroup G) ⊓ centralizer (normalizerMoved L : Set G)) ∈
        Chapter1.L G (T : Subgroup G) ∧
      (solvableRadical L).map L.subtype ⊔
        normalizerResidual L ((T : Subgroup G) ⊓ centralizer (normalizerMoved L : Set G)) = L := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  obtain ⟨he,hne,hcore,hN⟩ := faithful_maximal_normalizer_moved h.simpleQTKE hL hTL
  let := he
  have hUT : normalizerMoved L ≤ (T : Subgroup G) := by
    apply hcore.trans
    have hh := pCoreIn_le_sylow (normalizer (L : Set G)) (T.subtype hTL)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTL] at hh
  apply centralizer_normalizerResidual_mem_L_and_supplement T L (normalizerMoved L) hL.1.1 hTL
    (by rw [hN]; exact L.le_normalizer) (by rwa [hN]) hUT
    (le_centralizer _) hne (normalizerMoved_commutator_and_card hL.1.1 hne).1

/-- Original 13.1.9 on radical supplements gives the precise uniqueness
required in 13.1.14 and E.3.35, at the full normalizer of C_T(U). -/
theorem normalizerMoved_centralizer_normalizer_unique
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hsupp : ∀ L₁ ∈ Chapter1.L G (T : Subgroup G),
      (solvableRadical L).map L.subtype ⊔ L₁ = L →
        maximalTwoLocalOvergroups (L₁ ⊔ (T : Subgroup G)) = {normalizer (L : Set G)}) :
    maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (normalizerMoved L : Set G) : Subgroup G) : Set G)) =
        {normalizer (L : Set G)} := by
  let U := normalizerMoved L
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let Y := normalizerResidual L R
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  obtain ⟨he,hne,hcore,hN⟩ := faithful_maximal_normalizer_moved h.simpleQTKE hL hTL
  let := he
  have hUT : U ≤ (T : Subgroup G) := by
    apply hcore.trans
    have hh := pCoreIn_le_sylow (normalizer (L : Set G)) (T.subtype hTL)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTL] at hh
  have hRne : R ≠ ⊥ := by
    intro hb
    exact hne (bot_unique (hb ▸ le_inf hUT (le_centralizer U)))
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) := by rw [hN];exact hTL
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (hTU.trans (le_normalizer_of_normal_subgroupOf
        (centralizer_le_normalizer (U : Set G))))).trans inf_normalizer_le_normalizer_inf
  have hYTN : Y ⊔ (T : Subgroup G) ≤ normalizer (R : Set G) :=
    sup_le (normalizerResidual_le_normalizer L R) hTR
  have hf := normalizerMoved_frattini_supplement h hL hn
  have hu := hsupp Y hf.1 hf.2
  have hlocal : IsTwoLocal (normalizer (R : Set G)) :=
    ⟨R,hRne,T.isPGroup'.to_le inf_le_left,rfl⟩
  obtain ⟨K,hNK,hK⟩ := Finite.exists_le_maximal hlocal
  have hKM : K = normalizer (L : Set G) :=
    Set.mem_singleton_iff.mp (hu ▸ (show K ∈ maximalTwoLocalOvergroups
      (Y ⊔ (T : Subgroup G)) from ⟨hK,hYTN.trans hNK⟩))
  have hNM : normalizer (R : Set G) ≤ normalizer (L : Set G) := hKM ▸ hNK
  ext J
  constructor
  · intro hJ
    exact hu ▸ (show J ∈ maximalTwoLocalOvergroups (Y ⊔ (T : Subgroup G)) from
      ⟨hJ.1,hYTN.trans hJ.2⟩)
  · intro hJ
    have hj := Set.mem_singleton_iff.mp hJ
    subst J
    exact ⟨hKM ▸ hK,hNM⟩

/-- The normalizer clause of original 13.1.14 on the literal moved module,
with normalizer uniqueness discharged by the actual Frattini supplement.
Only the permitted original 13.1.9 supplement-uniqueness premise remains. -/
theorem normalizer_weakClosure_zero_le_of_supplements
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hTI : ChapterI.Section06To08.IsTISubgroup (normalizerMoved L))
    (hsupp : ∀ L₁ ∈ Chapter1.L G (T : Subgroup G),
      (solvableRadical L).map L.subtype ⊔ L₁ = L →
        maximalTwoLocalOvergroups (L₁ ⊔ (T : Subgroup G)) = {normalizer (L : Set G)}) :
    normalizer (ChapterE.indexedWeakClosure (normalizerMoved L) (T : Subgroup G) 0 : Set G) ≤
      normalizer (L : Set G) :=
  normalizer_weakClosure_zero_le h hmany hL hn hTI
    (normalizerMoved_centralizer_normalizer_unique h hL hn hsupp)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal
