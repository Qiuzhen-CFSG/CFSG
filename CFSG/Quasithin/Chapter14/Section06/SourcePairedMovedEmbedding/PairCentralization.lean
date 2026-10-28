module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding.NonnormalModels
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding.ModelExclusion
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OrdinaryContainment
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import Theory.GroupTheory.Amalgam.LocalStructure
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115

/-!
# Centralization by a conjugate pair of deleted alternating-five blocks

A local block either lies in an ordinary component or centralizes it.
Containment forces the ordinary component to be normal, by the full 1.2.1
nonnormal catalogue. It then contains both conjugate blocks. The actual
pair order, core sizes and local Sylow marking exclude every marked 1.1.5
model, so containment is impossible for either block.

Source: Aschbacher--Smith 1.2.8(1--2), printed pp.506--507, as used in
14.6.9, printed p.1026.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding
open ChapterC ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Chapter15.Section03.Candidates.ComponentStructure
universe u
variable {X : Type u} [Group X] [Finite X]

theorem local_conjugate_deleted_pair_centralizes_ordinary
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (B C : Subgroup X)
    (hB : B ∈ localCComponents S) (hC : C ∈ localCComponents S)
    (hb : IsAlternatingBlock B 5) (hc : IsAlternatingBlock C 5)
    (hbc : Nat.card (pCore 2 B) = 16) (hcc : Nat.card (pCore 2 C) = 16)
    (hcomm : ⁅B,C⁆ = ⊥)
    (hswap : ∃ t : X, B.map (MulAut.conj t).toMonoidHom = C)
    (A : Subgroup X) (hA : IsComponent X A)
    (hmodel : ∃ α : MulAut A, ModelAction115 A α) :
    B ⊔ C ≤ centralizer (A : Set X) := by
  have hex (hBA : B ≤ A) (hCA : C ≤ A) : False := by
    obtain ⟨SA,_,hl⟩ := exists_local_sylow_restriction S hB hBA hA.1
    let : IsQuasisimple A := hA.2
    let eb := subgroupOfEquivOfLe hBA
    let ec := subgroupOfEquivOfLe hCA
    have hb' := RankOne.Solvable.isAlternatingBlock_of_equiv eb.symm hb
    have hc' := RankOne.Solvable.isAlternatingBlock_of_equiv ec.symm hc
    have hbc' : Nat.card (pCore 2 (B.subgroupOf A)) = 16 :=
      (LocalCoreTransport.core_card 2 eb).trans hbc
    have hcc' : Nat.card (pCore 2 (C.subgroupOf A)) = 16 :=
      (LocalCoreTransport.core_card 2 ec).trans hcc
    have hcomm' : ⁅B.subgroupOf A,C.subgroupOf A⁆ = ⊥ := by
      apply map_injective A.subtype_injective
      rw [map_commutator,map_subgroupOf_eq_of_le hBA,map_subgroupOf_eq_of_le hCA,
        hcomm,Subgroup.map_bot]
    obtain ⟨α,hm⟩ := hmodel
    exact not_modelAction115_of_commuting_deleted_pair SA (B.subgroupOf A) (C.subgroupOf A) hl hb' hc' hbc' hcc' hcomm' hm
  obtain ⟨t,ht⟩ := hswap
  apply sup_le
  · rcases local_ordinary_dichotomy hX S hB hA with hBA | hcentral
    · let : A.Normal := ordinary_component_normal_of_contained_alternating_five hX S B hB hb A hA hBA
      have hCA : C ≤ A := by
        rw [←ht]
        exact (map_mono hBA).trans_eq (mem_normalizer_iff_map_conj_eq.mp
          (show t ∈ normalizer (A : Set X) from by simp [normalizer_eq_top]))
      exact (hex hBA hCA).elim
    · exact hcentral
  · rcases local_ordinary_dichotomy hX S hC hA with hCA | hcentral
    · let : A.Normal := ordinary_component_normal_of_contained_alternating_five hX S C hC hc A hA hCA
      have hBA : B ≤ A := by
        intro b hb
        have htbt : t * b * t⁻¹ ∈ A := hCA (ht ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hb)
        have h := Subgroup.Normal.conj_mem (inferInstance : A.Normal) _ htbt t⁻¹
        simpa only [mul_assoc,inv_mul_cancel_left,inv_inv,mul_inv_cancel_right,inv_mul_cancel,mul_one] using h
      exact (hex hBA hCA).elim
    · exact hcentral

end CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding
