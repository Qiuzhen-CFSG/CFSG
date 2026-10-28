module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.SmallChiefRecognition
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.ActorStructure

/-!
# Applying the small-chief sieve to the original A₅ overcomponent

The source construction supplies the same literal layer, faithful actor and
marked involution used by the representation exclusions. The only model
input is the local-embedding shortlist for the original head I/O₂(I).
The output distinguishes that head, which may retain a central three,
from its faithful actor, which is A₇.

Source: Aschbacher–Smith 10.2.1, printed p.743. The shortlist and the
remaining central-three exclusion belong to the local/final assembly.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open Chapter3.Section02 ChapterC Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original source action discharges every small-chief hypothesis in the
conditional local-shortlist sieve. -/
theorem source_a5_involution_overcomponent_head_and_actor_seven_of_shortlist
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {v : G} (hv : orderOf v = 2) {I : Subgroup G} (hLI : L ≤ I)
    (hIX : I ≤ centralizer ({v}:Set G))
    (hI : (I.subgroupOf (centralizer ({v}:Set G))).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G))
      (centralizer ({v}:Set G)))
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I)
    (hhead : IsQuasisimple (I ⧸ pCore 2 I))
    (hlist : let H := I ⧸ pCore 2 I
      IsAlternating H 7 ∨ IsAlternatingCover H 7 ∨ Nonempty (H ≃* Janko1.Model) ∨
      ClassicalGroup.IsPSL H 2 25 ∨ ∃ p, A312ExceptionalPrime p ∧ ClassicalGroup.IsPSL H 2 p) :
    (IsAlternating (I ⧸ pCore 2 I) 7 ∨ IsAlternatingCover (I ⧸ pCore 2 I) 7) ∧
      Nonempty ((I ⧸ centralizer (normalClosure
        ((blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype : Set I) : Set I)) ≃*
        alternatingGroup (Fin 7)) := by
  let K := L.subgroupOf I
  let W := normalClosure ((blockU K).map K.subtype : Set I)
  let A := I ⧸ centralizer (W:Set I)
  let q := QuotientGroup.mk' (centralizer (W:Set I))
  let := hhead
  obtain ⟨hquasi,_,_,_,_,⟨ec⟩⟩ := source_a5_overcomponent_quasisimple_head_action
    D e hn hout hLI hIX hI hS hU hhead
  let : IsQuasisimple A := hquasi
  obtain ⟨he,t,hh,ht,hr,_⟩ := source_a5_involution_overcomponent_chief_action
    D e hn hout hv hLI hIX hI hS hU
  let := he
  let ρ := Representation.NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let σ := Representation.BinaryOffender.fixedQuotient ρ ⊤
  exact head_and_actor_seven_of_small_chief σ hh t ht hr ec hlist

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
