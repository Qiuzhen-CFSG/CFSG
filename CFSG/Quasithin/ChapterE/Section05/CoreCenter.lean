module

public import CFSG.Quasithin.ChapterE.Section05.CoreCenter.Thompson
public import CFSG.Quasithin.ChapterE.Section05.CoreCenter.OddRadical
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.SolvableRadical.Transport

/-!
# E.5.1: the higher Thompson center and the local core

The Thompson rank argument proves that D centralizes W and O₂(K)/W.
The full two-layer fixer is normal in K. Its two-residual centralizes
O₂(K), so the source centralizer bound puts that residual in R. If
O₂(K/R) is trivial, the fixer lies in R. Two-closedness of R now puts
the elementary subgroup D in O₂(K), and the omega-centralizer identity
puts it in Ω₁(Z(W)).

The structural premises on R are discharged in both source branches:
`CoreCenter.OddRadical` supplies them for the literal Frattini preimage
in E1, and the solvable radical supplies them in E2. Thus the final
center-containment theorem uses only the source hypotheses. Together with
`proposition_E_5_1_normality` from `Section05.Basic`, it proves E.5.1.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, Proposition E.5.1, printed p.242.
-/

open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterE
open ChapterB
variable {G : Type*} [Group G] [Finite G]

private theorem two_subgroup_le_core {N U : Subgroup G} [N.Normal]
    (hN : IsTwoClosed N) (hU : IsPGroup 2 U) (hUN : U ≤ N) : U ≤ pCore 2 G := by
  obtain ⟨S, hS⟩ := hN
  let _ : (S : Subgroup N).Characteristic := S.characteristic_of_normal hS
  have hsn : ((S : Subgroup N).map N.subtype).Normal := inferInstance
  have hle : U.subgroupOf N ≤ (S : Subgroup N) := by
    let _ := hS
    have hpg := hU.comap_of_injective N.subtype N.subtype_injective
    obtain ⟨T, hT⟩ := hpg.exists_le_sylow
    have hST : S = T := by
      apply Sylow.ext
      exact (S.is_maximal' T.isPGroup' (S.isPGroup'.le_sylow_of_normal T)).symm
    simpa only [hST, subgroupOf] using hT
  calc
    U = (U.subgroupOf N).map N.subtype := (map_subgroupOf_eq_of_le hUN).symm
    _ ≤ (S : Subgroup N).map N.subtype := map_mono hle
    _ ≤ pCore 2 G := le_sSup ⟨hsn, S.isPGroup'.map N.subtype⟩

/-- The center assertion of E.5.1 from the precise structural properties of R.
These additional radical premises remain explicit. -/
public theorem higherThompsonCenter_le_omegaCenter_of_radical
    (P A K : Subgroup G) (i j : ℕ)
    (hA : A ∈ thompsonFamily P i) (hK : IsEMemberAt j P A K)
    (R : Subgroup K) [R.Normal] (hR : IsTwoClosed R)
    (hquot : pCore 2 (K ⧸ R) = ⊥)
    (hcent : pResidual 2 K ⊓ centralizer (pCore 2 K : Set K) ≤ R) :
    higherThompsonCenter P (i + j) ≤
      omegaOneCenterAmbient (higherThompsonCore P K (i + j)) := by
  by_cases hdeg : twoRank P ≤ i + j
  · rw [higherThompsonCenter_eq_bot_of_rank_le P (i + j) hdeg]
    exact bot_le
  have hij : i + j < twoRank P := Nat.lt_of_not_ge hdeg
  let D := higherThompsonCenter P (i + j)
  let W := higherThompsonCore P K (i + j)
  have hDK : D ≤ K := higherThompsonCenter_le_member P A K i j hA hK.1 hij
  have hWK : W ≤ K := higherThompsonCore_le P K (i + j)
  let d := D.subgroupOf K
  let w := W.subgroupOf K
  let _ : w.Normal := higherThompsonCore_normal P K (i + j) hK.1.core_le
  have hwQ : w ≤ pCore 2 K := by
    intro x hx
    obtain ⟨q, hq, he⟩ := higherThompsonCore_le_core P K (i + j) hx
    exact (show q = x from Subtype.ext he) ▸ hq
  have hdw : d ≤ centralizer (w : Set K) := by
    intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    apply Subtype.ext
    exact mem_centralizer_iff.mp
      ((centralizer_le (higherThompsonCore_le_thompsonJ P K (i + j)))
        (higherThompsonCenter_centralizes P (i + j) hx)) y hy
  have hcomm : ⁅d, pCore 2 K⁆ ≤ w := by
    apply (map_le_map_iff_of_injective K.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le hDK, map_subgroupOf_eq_of_le hWK]
    exact higherThompsonCenter_commutator_core_le P A K i j hA hij hK
  have hdR : d ≤ R :=
    (le_inf hdw (le_commutatorPreimage le_top hcomm)).trans
      (two_layer_le_radical (pCore 2 K) w R (pCore_isPGroup.to_le hwQ) hquot hcent)
  let _ : IsElementaryAbelian 2 D := omegaOneCenterAmbient_elementaryAbelian _
  have hdQ : d ≤ pCore 2 K := two_subgroup_le_core hR
    ((IsElementaryAbelian.isPGroup 2 D).comap_subtype) hdR
  have hDQ : D ≤ (pCore 2 K).map K.subtype := by
    intro x hx
    exact ⟨⟨x, hDK hx⟩, hdQ hx, rfl⟩
  intro x hx
  refine (mem_omegaOneCenterAmbient_iff W x).mpr ⟨?_, ?_, ?_⟩
  · exact higherThompsonCenter_inf_core_le P A K i j hA hij hK ⟨hx, hDQ hx⟩
  · exact ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.1
  · exact mem_centralizer_iff.mp
      ((centralizer_le (higherThompsonCore_le_thompsonJ P K (i + j)))
        (higherThompsonCenter_centralizes P (i + j) hx))

/-- The E2 component branch of the center assertion in E.5.1. -/
public theorem proposition_E_5_1_center_component
    (P : Sylow 2 G) (A K : Subgroup G) (i j : ℕ)
    (hA : A ∈ thompsonFamily (P : Subgroup G) i)
    (hK : IsEMemberAt j (P : Subgroup G) A K)
    (hc : ECaseComponent (P : Subgroup G) A K)
    (hcent : pResidual 2 K ⊓ centralizer (pCore 2 K : Set K) ≤ solvableRadical K) :
    higherThompsonCenter (P : Subgroup G) (i + j) ≤
      omegaOneCenterAmbient (higherThompsonCore (P : Subgroup G) K (i + j)) := by
  apply higherThompsonCenter_le_omegaCenter_of_radical (P : Subgroup G) A K i j hA hK
    (solvableRadical K) hc.1 _ hcent
  let H := K ⧸ solvableRadical K
  have : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hle : pCore 2 H ≤ solvableRadical H :=
    le_solvableRadical _ inferInstance inferInstance
  exact bot_unique (hle.trans_eq solvableRadical_quotient_solvableRadical)

/-- The higher Thompson center lies in the omega-center of the local core
under the source residual-centralizer bound. The proof also permits `j = 0`. -/
public theorem higherThompsonCenter_le_omegaCenter
    (P : Sylow 2 G) (A K : Subgroup G) (i j : ℕ)
    (hA : A ∈ thompsonFamily (P : Subgroup G) i)
    (hK : IsEMemberAt j (P : Subgroup G) A K)
    (hcent : WeakClosureCentralizerBound (P : Subgroup G) A K) :
    higherThompsonCenter (P : Subgroup G) (i + j) ≤
      omegaOneCenterAmbient (higherThompsonCore (P : Subgroup G) K (i + j)) := by
  rcases hcent with ⟨ho, hc⟩ | ⟨he, hc⟩
  · exact higherThompsonCenter_le_omegaCenter_of_radical (P : Subgroup G) A K i j
      hA hK (weakClosureOddRadical K) ho.weakClosureOddRadical_twoClosed
      ho.pCore_quotient_weakClosureOddRadical hc
  · exact proposition_E_5_1_center_component P A K i j hA hK he hc

/-- Proposition E.5.1, center-containment clause, with the source's positive
index. The other clause is `proposition_E_5_1_normality`. -/
public theorem proposition_E_5_1_center
    (P : Sylow 2 G) (A K : Subgroup G) (i j : ℕ) (_hj : 0 < j)
    (hA : A ∈ thompsonFamily (P : Subgroup G) i)
    (hK : IsEMemberAt j (P : Subgroup G) A K)
    (hcent : WeakClosureCentralizerBound (P : Subgroup G) A K) :
    higherThompsonCenter (P : Subgroup G) (i + j) ≤
      omegaOneCenterAmbient (higherThompsonCore (P : Subgroup G) K (i + j)) :=
  higherThompsonCenter_le_omegaCenter P A K i j hA hK hcent

end CFSG.Quasithin.ChapterE
