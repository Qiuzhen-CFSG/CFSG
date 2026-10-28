module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableSeedAction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneComparison
public import Theory.GroupTheory.PrimeRankOrderBound

/-!
# Kernel equality and the central test plane after S3 recognition

B.5's actual S3 row splits VH into its K-commutator plane and its K-fixed
space. The surjection K/C_K(VH) onto the original dotted K becomes injective
once both groups are identified with S3, giving the literal kernel equality
C_K(VH) = C_K(U-hat). The equivalence with the action image and every quotient
map are those constructed in SolvableSeedAction and SolvableSeed.

The source application transports the B.5 decomposition back to the original
commutator subgroup in additive coordinates. It retains an explicit S3 model
for the VH-action. Constructing that model from the classified alternatives,
extending this decomposition to Z(U), and the final contradiction remain
with the centerlessness owner. These conditional conclusions do not prove
14.3.25 or centerlessness.

Source: Aschbacher--Smith 14.3.25, printed p.1001, and B.5.6(2), p.105.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem symmetricThree_case {D X : Type*} [Group D] [Finite D]
    [AddCommGroup X] [Module (ZMod 2) X] (ρ : Representation (ZMod 2) D X)
    (hc : NontrivialAdequateAlternative ρ) (e : D ≃* Equiv.Perm (Fin 3)) :
    Nonempty (SymmetricThreeCase ρ) := by
  have hcard : Nat.card D = 6 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hr : primeRank 3 D ≤ 1 := primeRank_le_of_prime_pow_not_dvd (by rw [hcard]; decide)
  rcases hc.at_three_rank_le_one hr with ⟨hq,_⟩ | hs
  · let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
    let := hq
    let : IsSimpleGroup (generalizedFitting D ⧸ center (generalizedFitting D)) :=
      IsQuasisimple.simple
    let : Nontrivial (generalizedFitting D) :=
      (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial
    exact (Group.IsPerfect.not_isSolvable (generalizedFitting D) inferInstance).elim
  · exact hs

/-- Identifying the actual VH-action with S3 forces equality of the two
literal kernels. The previously constructed surjection alone is not used
as an isomorphism. -/
theorem source_solvable_seed_kernel_eq_of_model (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (row : SolvableSeedRow F L g)
    (hn : ((faithfulTestModule F L).subgroupOf F.H).Normal)
    (model : letI := hn
      Nonempty (((solvableSeedActor F g).map (QuotientGroup.mk' (centralizer
        ((faithfulTestModule F L).subgroupOf F.H : Set F.H)))) ≃* Equiv.Perm (Fin 3))) :
    (centralizer ((faithfulTestModule F L).subgroupOf F.H : Set F.H)).comap
        (solvableSeedActor F g).subtype =
      (F.uhatAction.comp (solvableSeedActor F g).subtype).ker := by
  let := hn
  let K := solvableSeedActor F g
  let C := (centralizer ((faithfulTestModule F L).subgroupOf F.H : Set F.H)).comap K.subtype
  obtain ⟨hnC,f,hf,heval,hemodel⟩ := source_solvable_seed_quotient d earlier hq chosen
    structural alternatives F hne hz g hgP row
  let := hnC
  obtain ⟨e,he⟩ := solvable_seed_action_equiv (L := L) F g hn
  obtain ⟨em⟩ := model
  obtain ⟨ed⟩ := hemodel
  have hc : Nat.card (K ⧸ C) = Nat.card (K.map (QuotientGroup.mk' F.uhatAction.ker)) :=
    Nat.card_congr ((e.trans em).trans ed.symm).toEquiv
  have hi : Function.Injective f := (hf.bijective_of_nat_card_le hc.le).1
  apply le_antisymm
  · exact source_solvable_seed_kernel_comparison d earlier hq chosen structural alternatives
      F hne hz g hgP row
  · intro k hk
    have hfq : f (QuotientGroup.mk' C k) = 1 := by
      apply Subtype.ext
      rw [heval]
      exact (QuotientGroup.eq_one_iff (k : F.H)).mpr hk
    exact (QuotientGroup.eq_one_iff k).mp (hi (hfq.trans f.map_one.symm))

/-- The S3 action row yields a genuine split central test module: its
commutator plane has dimension two and its complement is the original
K-centralizer in VH. No splitting of the whole Z(U) is assumed here. -/
theorem source_solvable_seed_plane_of_model (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g)
    (hn : ((faithfulTestModule F L).subgroupOf F.H).Normal)
    (he : IsElementaryAbelian 2 ((faithfulTestModule F L).subgroupOf F.H))
    (model : letI := hn
      Nonempty (((solvableSeedActor F g).map (QuotientGroup.mk' (centralizer
        ((faithfulTestModule F L).subgroupOf F.H : Set F.H)))) ≃* Equiv.Perm (Fin 3))) :
    letI := hn; letI := he
    let W := (faithfulTestModule F L).subgroupOf F.H
    let K := solvableSeedActor F g
    IsCompl (NormalElementaryQuotient.commutatorSpace W K)
      (fixedSpace (NormalElementaryQuotient.originalAction W) K) ∧
      Module.finrank (ZMod 2) (NormalElementaryQuotient.commutatorSpace W K) = 2 := by
  let := hn
  let := he
  dsimp only
  let W := (faithfulTestModule F L).subgroupOf F.H
  let K := solvableSeedActor F g
  let C := centralizer (W : Set F.H)
  let q := QuotientGroup.mk' C
  let D := K.map q
  let σ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨_,_,_,hc⟩ := source_solvable_seed_classification d earlier hq chosen structural
    alternatives F hne hz g hgP hgH row
  obtain ⟨em⟩ := model
  obtain ⟨cs⟩ := symmetricThree_case (σ.comp D.subtype) hc em
  have hσ : σ.comp q = NormalElementaryQuotient.originalAction W := by
    apply MonoidHom.ext
    intro b
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) b w).trans
        (NormalElementaryQuotient.originalAction_apply W b w).symm
  have hm : ChapterB.QuasisimpleSource.moved (σ.comp D.subtype) ⊤ =
      NormalElementaryQuotient.commutatorSpace W K := by
    rw [NormalElementaryQuotient.original_moved_space,←hσ,subspaceCommutator_comp_map]
    change subspaceCommutator (σ.comp D.subtype) ⊤ ⊤ = _
    rw [subspaceCommutator_comp_map,← MonoidHom.range_eq_map,Subgroup.range_subtype]
  have hfix : Representation.invariants (σ.comp D.subtype) =
      fixedSpace (NormalElementaryQuotient.originalAction W) K := by
    rw [←hσ,fixedSpace_comp_map]
    rfl
  change IsCompl (NormalElementaryQuotient.commutatorSpace W K)
    (fixedSpace (NormalElementaryQuotient.originalAction W) K) ∧
    Module.finrank (ZMod 2) (NormalElementaryQuotient.commutatorSpace W K) = 2
  rw [←hm,←hfix]
  exact ⟨cs.decomposition,cs.dimension⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
