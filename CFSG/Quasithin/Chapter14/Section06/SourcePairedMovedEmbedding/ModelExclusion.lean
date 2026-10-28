module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedEvenPair
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding.SmallModels
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding.SporadicModels
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding.PairNumerics


/-!
# No commuting deleted pair in an ordinary marked component

The original two blocks each retain their deleted four-dimensional module.
Their core-order hypothesis identifies the entire core with that module,
so the blocks are centerless. Their commuting product therefore embeds in
the ordinary component and in its central two-core quotient. The same maps
force product order960² and two-rank at least eight in the quotient.

An elementary sixteen excludes the small alternating and odd rows of
1.1.5. The full-Sylow even-family dispatcher excludes the Lie rows and
the PSL₃(4)/G₂(4) central-cover rows. The quotient rank and order exclude
every sporadic row. The original automorphism remains the one marked by
ModelAction115; neither minimal-parabolic nor block-invariance assumptions
are introduced.

Source: Aschbacher–Smith, 14.6.9 at N(D), printed p.1026, using the
moved-pair obstruction in 1.2.8(1–2), printed pp.506–507.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding
open ChapterC Chapter15.Section03.Candidates.ComponentStructure
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

private theorem rank_two_image_excluded
    {A Q : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    (f : A →* Q) (hf : Function.Surjective f) (hker : Group.IsSolvable f.ker)
    (S : Sylow 2 A) (B : Subgroup A) (hB : B ∈ localCComponents S)
    (hc : Nat.card B = 960) (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hi : Function.Injective (f.subgroupMap B)) (hp : 921600 ∣ Nat.card Q)
    (hm : Chapter1.Section02.LocalModels.RankTwoTheoremC Q) : False := by
  let := hker
  let d : B ≃* B.map f := MulEquiv.ofBijective (f.subgroupMap B)
    ⟨hi, f.subgroupMap_surjective B⟩
  apply AlternatingFiveDeletedEvenPair.not_rank_two
    (S.mapSurjective hf) (B.map f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB f)
    ((Nat.card_congr d.toEquiv).symm.trans hc)
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans e) hp hm

private theorem not_model_of_numerics
    {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (S : Sylow 2 A) (B : Subgroup A) (hB : B ∈ localCComponents S)
    (hc : Nat.card B = 960) (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (E : Subgroup A) (hE : IsElementaryAbelian 2 E) (hEc : 16 ≤ Nat.card E)
    (hpair : 921600 ∣ Nat.card A)
    (hqi : Function.Injective ((QuotientGroup.mk' (pCore 2 A)).subgroupMap B))
    (hqp : 921600 ∣ Nat.card (A ⧸ pCore 2 A))
    (hqr : 8 ≤ primeRank 2 (A ⧸ pCore 2 A))
    {α : MulAut A} (hm : ModelAction115 A α) : False := by
  rcases modelAction115_large_elementary_cases E hE hEc hm with
    ⟨_, hl, _⟩ | ⟨_, _, hl, _⟩ | ⟨name, hn, he, _⟩
  · exact AlternatingFiveDeletedEvenPair.not_lie_type_two S B hB hc e hpair hl
  · let q := QuotientGroup.mk' (pCore 2 A)
    have hks : Group.IsSolvable q.ker := by
      change Group.IsSolvable (QuotientGroup.mk' (pCore 2 A)).ker
      rw [QuotientGroup.ker_mk']
      let : Group.IsNilpotent (pCore 2 A) := pCore_isNilpotent
      infer_instance
    apply rank_two_image_excluded q (QuotientGroup.mk'_surjective _) hks
      S B hB hc e hqi hqp
    rcases hl with hl | hl
    · exact .linear 2 (by decide) (by simpa only [show (2:ℕ)^2 = 4 by rfl] using hl)
    · exact .g2 2 (by decide) (by simpa only [show (2:ℕ)^2 = 4 by rfl] using hl)
  · exact not_sporadic_model_of_pair_numerics hqr
      ((by decide : 25 ∣ 921600).trans hqp) name hn he


/-- The source core-equality formulation excludes every original marked ordinary row. -/
theorem not_modelAction115_of_commuting_deleted_pair_core_eq
    {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (S : Sylow 2 A) (B C : Subgroup A) (hB : B ∈ localCComponents S)
    (hb : IsAlternatingBlock B 5) (hc : IsAlternatingBlock C 5)
    (hbc : pCore 2 B = blockU B) (hcc : pCore 2 C = blockU C)
    (hcomm : B ≤ centralizer (C : Set A))
    {α : MulAut A} (hm : ModelAction115 A α) : False := by
  let q := QuotientGroup.mk' (pCore 2 A)
  have hqker : q.ker ≤ center A := by
    change (QuotientGroup.mk' (pCore 2 A)).ker ≤ center A
    rw [QuotientGroup.ker_mk']
    exact IsQuasisimple.pCore_le_center 2
  have hidker : (MonoidHom.id A).ker ≤ center A := by simp
  obtain ⟨_, _, hpair⟩ := paired_numerics_of_central_ker B C hb hc hbc hcc hcomm
    (MonoidHom.id A) hidker
  obtain ⟨hrank, _, hqpair⟩ := paired_numerics_of_central_ker B C hb hc hbc hcc hcomm q hqker
  have hinj := block_comp_injective_of_central_ker B hb hbc q hqker
  have hrestricted : Function.Injective (q.subgroupMap B) := by
    intro b c h
    exact hinj (congrArg Subtype.val h)
  let E := (blockU B).map B.subtype
  have hE : IsElementaryAbelian 2 E := hb.2.1.elementary.map B.subtype
  have hEc : 16 ≤ Nat.card E := by
    rw [show E = (blockU B).map B.subtype from rfl,
      card_map_of_injective B.subtype_injective, hb.blockU_card]
  exact not_model_of_numerics S B hB (block_card_eq_960 hb hbc)
    hb.2.2.quotient_iso.some E hE hEc hpair hrestricted hqpair hrank hm

/-- Two commuting deleted alternating-five blocks with literal cores of order sixteen
cannot both lie in an ordinary component carrying the full original 1.1.5 marking.
The first block retains its local-component marking for the component's full Sylow. -/
theorem not_modelAction115_of_commuting_deleted_pair
    {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (S : Sylow 2 A) (B C : Subgroup A) (hB : B ∈ localCComponents S)
    (hb : IsAlternatingBlock B 5) (hc : IsAlternatingBlock C 5)
    (hbc : Nat.card (pCore 2 B) = 16) (hcc : Nat.card (pCore 2 C) = 16)
    (hcomm : ⁅B, C⁆ = ⊥)
    {α : MulAut A} (hm : ModelAction115 A α) : False := by
  exact not_modelAction115_of_commuting_deleted_pair_core_eq S B C hB hb hc
    (block_core_eq_blockU_of_card_sixteen hb hbc)
    (block_core_eq_blockU_of_card_sixteen hc hcc)
    (commutator_eq_bot_iff_le_centralizer.mp hcomm) hm

end CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding
