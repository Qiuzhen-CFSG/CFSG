module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.PairedNormalizer.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.PairedNormalizer.Members
public import Theory.GroupTheory.GeneralizedFitting.PairedOrbitActorRank
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure

/-!
# The paired local-normalizer branch of E.1.11

An escaping local normalizer must equal its simple component, making the
local weak closure centralize that component. A family member escaping
the component stabilizer therefore has a centralizing stabilizer. Its
rank is one, and its full tau orbit supplies an actual E-member containing
the component. This contradicts the assumed escape.

All subgroups remain those of the original family. The proof does not use
the false general actor-transfer interface. The actual solvable maximal
overgroup is an explicit earlier source input.

Source: Aschbacher–Smith, E.1.11, p.214, in the paired E.2.2 case.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

theorem localNormalizer_le_of_paired_solvable_max {n : ℕ} (hn : 0 < n)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    [Group.IsSolvable (ChapterB.minimalParabolicMax T hP)]
    {K : Subgroup G} (hK : IsComponent G K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (hrad : solvableRadical G = ⊥) (hlayer : pResidual 2 G = componentLayer G)
    (hindex : (normalizer (K : Set G)).index = 2)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    localNormalizer T K Ω ≤ generationTarget n T Ω := by
  by_contra hnot
  have he := pairedNormalizer_eq_component_of_escape hn T hP hK hΩ hnot
  have hc := localWeakClosure_centralizes_of_localNormalizer_eq T hK hΩ he
  obtain ⟨A,hA,hAT,hAS⟩ := exists_member_not_le_stabilizer T K hΩ hnot
  let : IsElementaryAbelian 2 A := hΩ.1 A hA
  have hm : ¬ A ≤ normalizer (K : Set G) := fun h => hAS (le_inf hAT h)
  have hfix : A ⊓ normalizer (K : Set G) ≤ centralizer (K : Set G) := by
    apply le_trans _ ((inf_stabilizer_le_localWeakClosure T K hA hAT).trans hc)
    intro x hx
    exact ⟨hx.1,hAT hx.1,hx.2⟩
  have hr := rank_one_of_moved_pair_and_fixed_stabilizer T hK hgen hlayer
    (SimpleSocle.pCore_eq_bot hrad 2) hindex hAT hm hfix
  have htA : A ≤ tau (T : Subgroup G) A := le_sup_left.trans (sup_pCore_le_tau T A hAT)
  have ho := moved_pair_orbit_eq_residual T hK hgen hlayer hindex
    (show ¬ tau (T : Subgroup G) A ≤ normalizer (K : Set G) from fun h => hm (htA.trans h))
  have hmem := tau_join_member_of_full_orbit T hK hrad hlayer hAT ho (Or.inr ⟨hm,hr⟩)
    (show Group.rank A ≤ n by omega)
  apply hnot
  have hX : K ⊔ tau (T : Subgroup G) A ≤ eSubgroup n (T : Subgroup G) A := le_sSup hmem
  exact inf_le_left.trans (le_sup_left.trans (hX.trans
    ((le_iSup (fun B : {B : Subgroup G // B ∈ Ω ∧ B ≤ (T : Subgroup G)} =>
      eSubgroup n (T : Subgroup G) B.1) ⟨A,hA,hAT⟩).trans le_sup_left)))

end CFSG.Quasithin.ChapterE.ChiefOrbit
