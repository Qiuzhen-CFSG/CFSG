module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.ActorStructure
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.PrimeActorParameters
/-!
# The original contained-layer head is quasisimple

A nonquasisimple head has a prime-field PSL₂ actor. The marked chief
action forces p=5 or p=7. The original A₅ image excludes p=7 by order,
while the source point-residual argument excludes p=5. Thus the head
I/O₂(I) is quasisimple, with the same actual overcomponent and quotient.

Source: Aschbacher–Smith 10.2.1, printed p.743, using A.3.6 and B.4.5.
The no-A₅-actor input is discharged by the original-pair consumer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
theorem source_a5_involution_overcomponent_head_quasisimple
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {v : G} (hv : orderOf v=2) {I : Subgroup G} (hLI : L≤I)
    (hIX : I≤centralizer ({v}:Set G))
    (hI : (I.subgroupOf (centralizer ({v}:Set G))).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G))
      (centralizer ({v}:Set G)))
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype≤pCore 2 I)
    (hnot : ¬ Nonempty ((I ⧸ centralizer
      (normalClosure ((blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype:Set I):Set I))
      ≃* alternatingGroup (Fin 5))) : IsQuasisimple (I ⧸ pCore 2 I) := by
  obtain ⟨hquasi,hhead | ⟨p,hp,hp3,⟨ea⟩⟩⟩ :=
    source_a5_involution_overcomponent_actor_structure D e hn hout hv hLI hIX hI hS hU
  · exact hhead
  let K := L.subgroupOf I
  let W := normalClosure ((blockU K).map K.subtype:Set I)
  let A := I ⧸ centralizer (W:Set I)
  let q := QuotientGroup.mk' (centralizer (W:Set I))
  let := hquasi
  obtain ⟨he,t,hh,ht,hr,_⟩ :=
    source_a5_involution_overcomponent_chief_action D e hn hout hv hLI hIX hI hS hU
  let := he
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let σ := fixedQuotient ρ ⊤
  have hparams := prime_actor_parameters_of_small_involution σ hh t ht hr hp hp3 ea
  rcases hparams with rfl | rfl
  · exact (hnot ⟨ea.trans Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some⟩).elim
  · have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
    have hK : IsAlternatingBlock K 5 := hL.of_mulEquiv (subgroupOfEquivOfLe hLI).symm
    obtain ⟨S,_,hSK⟩ := source_containing_component_sylow hLI hIX hI hS
    have hs := hK.normalClosure_layer_split K S hSK hU
    obtain ⟨eb⟩ := hK.layer_split_quotient_image K W le_normalClosure hs.2.2.2.1 q
      (QuotientGroup.ker_mk' _)
    exact (not_prime_seven_actor_of_alternating_five_subgroup (K.map q) eb ⟨ea⟩).elim
end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
