module

public import CFSG.Quasithin.Chapter14.Section06.Singleton.E9Ambient.PointNormalizers
public import Theory.GroupTheory.CentralBinaryCentralizerCard

/-!
# Exact core action size in the elementary-nine source

The whole original span is elementary of order 32 and its core centralizer
inside that span is the original central line. Binary commutator duality
therefore gives core centralizer index 16 and core order at least 512.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- The original core acts with full binary dual order on the original span. -/
theorem source_singleton_nine_core_pairing_index
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let U := conjugateSpanBy (localModule T M) J
    let Q := J.pCoreIn 2
    let K := Q ⊓ centralizer (U : Set G)
    K.relIndex Q = 16 ∧ Nat.card Q = 16 * Nat.card K ∧ 512 ≤ Nat.card Q := by
  let U := conjugateSpanBy (localModule T M) J
  let Q := J.pCoreIn 2
  let Z := centralInvolutions T
  let K := Q ⊓ centralizer (U : Set G)
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  obtain ⟨_,_,⟨i⟩⟩ := source_rankTwo_critical_track_bounds
    hG T hempty hM hu hmany hcard e hab J hJ.1
  obtain ⟨hUm,hUcard⟩ := source_singleton_nine_whole_span_moved
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  change Nat.card U = 32 at hUcard
  have hUZ : U ⊓ centralizer (Q : Set G) = Z := by
    rw [show U = ⁅U,J⁆ from hUm]
    exact source_solvable_moved_core_centralizer hG T hempty hM hu hmany hcard e hab J hJ hs a
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hZcard : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  let : IsCyclic Z := isCyclic_of_prime_card hZcard
  have hZQ : ⁅Z,Q⁆ ≤ ⊥ := by
    apply (commutator_eq_bot_iff_le_centralizer.mpr ?_).le
    exact le_centralizer_iff.mp ((pCoreIn_le 2 J).trans h.H_centralizes)
  have hc := card_mul_card_centralizer_restrict_of_central_binary_pairing
    U Q Z hZU h.commutator_UH_QH_le_point hZQ hZcard
  have hKcard : Nat.card ((centralizer (U : Set G)).subgroupOf Q) = Nat.card K := by
    rw [←inf_subgroupOf_left,Nat.card_congr (subgroupOfEquivOfLe
      (show Q ⊓ centralizer (U : Set G) ≤ Q from inf_le_left)).toEquiv]
  have hZcard' : Nat.card ((centralizer (Q : Set G)).subgroupOf U) = 2 := by
    rw [←inf_subgroupOf_left,Nat.card_congr (subgroupOfEquivOfLe
      (show U ⊓ centralizer (Q : Set G) ≤ U from inf_le_left)).toEquiv,hUZ,hZcard]
  rw [hKcard,hZcard',hUcard] at hc
  have hQcard : Nat.card Q = 16 * Nat.card K := by omega
  have hcount := relIndex_mul_card_of_le (show K ≤ Q from inf_le_left)
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hidx : K.relIndex Q = 16 := by nlinarith
  have hUK : U ≤ K := le_inf h.UH_le_QH (le_centralizer U)
  have hKlow := card_le_of_le hUK
  rw [hUcard] at hKlow
  exact ⟨hidx,hQcard,by nlinarith [hQcard,hKlow]⟩

end CFSG.Quasithin.Chapter14.Section06
