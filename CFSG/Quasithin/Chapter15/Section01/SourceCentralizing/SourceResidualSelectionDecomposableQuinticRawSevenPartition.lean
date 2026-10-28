module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSevenGeometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SevenPartition.Membership

/-! The actual weight-two vector forces every three-pair preimage to escape
the original marked intersection and generate the same L with it. Native
partition geometry supplies one such preimage over the original full S,
with its complete characteristic-two/source-parabolic hypotheses. -/

public section
open Subgroup Equiv Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open AlternatingSeven.ThreeResidualLocals BinarySevenCode
open CaseIComponentData
variable {G : Type*} [Group G] [Finite G]

/-- Every literal three-pair preimage escapes the marked intersection and
generates the original component together with it. -/
theorem PreparedChosenModule.raw_seven_partition_generates
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (houtM : ¬K ≤ M)
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) K)
    (hb : IsAlternatingBlock K 7)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (p : Partition 7 4 ![2,2,2,1]) :
    let N := centralizer (Z1 : Set G) ⊓ Mc
    sevenPartitionPreimage K e p < K ∧
      ¬sevenPartitionPreimage K e p ≤ N ⊓ K ∧
      sevenPartitionPreimage K e p ⊔ (N ⊓ K) = K := by
  let N := centralizer (Z1 : Set G) ⊓ Mc
  obtain ⟨E,hE,u,hw,_,heq,hmax⟩ :=
    h.raw_seven_weight_two hG T hM hJ hu hZ hK houtM hi hb e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let f := (alternatingGroup (Fin 7)).subtype.comp q
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P0 := p.stabilizer.comap f
  let P := P0.map K.subtype
  let C := (N ⊓ K).subgroupOf K
  have hPL : P ≤ K := map_subtype_le _
  have hproper : P ≠ K := by
    intro he
    have hle : alternatingGroup (Fin 7) ≤ p.stabilizer := by
      intro g hg
      obtain ⟨k,hk⟩ := hq ⟨g,hg⟩
      have hh : (k : G) ∈ P := he.symm ▸ k.property
      obtain ⟨l,hl,hlk⟩ := hh
      have hlk' : l = k := Subtype.ext hlk
      subst l
      change f k ∈ p.stabilizer at hl
      have hf : f k = g := congrArg Subtype.val hk
      exact hf ▸ hl
    have hh := Subgroup.card_le_of_le hle
    rw [nat_card_alternatingGroup,Nat.card_fin,SevenPartition.stabilizer_card] at hh
    norm_num at hh
  let w := BinarySevenCode.evenWordsEquivCore.symm (E u).toAdd
  have hw' : weight w.val = 2 := hw
  obtain ⟨g,hg,hmove⟩ := SevenPartition.partition_moves_weight_two p w hw'
  obtain ⟨k,hk⟩ := hq ⟨g,hg.1⟩
  have hkP : k ∈ P0 := by
    change f k ∈ p.stabilizer
    have hf : f k = g := congrArg Subtype.val hk
    exact hf.symm ▸ hg.2
  have hnot : ¬ P0 ≤ C := by
    intro hle
    have hkc0 : (k : G) ∈ N ⊓ K := hle hkP
    have hkc : (k : G) ∈ centralizer ({((u : K) : G)} : Set G) :=
      (heq ▸ hkc0).2
    have hku : blockConjugate K k u = u := by
      apply Subtype.ext
      apply Subtype.ext
      change (k : G) * ((u : K) : G) * (k : G)⁻¹ = ((u : K) : G)
      rw [mem_centralizer_singleton_iff.mp hkc,mul_inv_cancel_right]
    have hh := hE k u
    rw [hku] at hh
    apply hmove
    apply Subtype.ext
    have hf : f k = g := congrArg Subtype.val hk
    change f k = g at hf
    change (fun i => w.val (g.symm i)) = w.val
    change E u = BinaryPermutation.SevenMarkedAction.coreAction (f k) (E u) at hh
    rw [hf] at hh
    exact congrArg (fun v : Multiplicative (BinaryPermutation.core (Fin 7)) => v.toAdd.val) hh.symm
  have hgen : P0 ⊔ C = ⊤ := by
    exact hmax.lt_iff.mp (lt_of_le_not_ge le_sup_right (fun hh => hnot (le_sup_left.trans hh)))
  have hC : C.map K.subtype = N ⊓ K := map_subgroupOf_eq_of_le inf_le_right
  refine ⟨lt_of_le_of_ne hPL hproper,?_,?_⟩
  · intro hle
    exact hnot fun k hk => hle (mem_map_of_mem K.subtype hk)
  · have hh := congrArg (fun A : Subgroup K => A.map K.subtype) hgen
    rw [Subgroup.map_sup,hC,←MonoidHom.range_eq_map,K.range_subtype] at hh
    exact hh

/-- A single original quotient marking supplies an actual S-normalized
source parabolic, its complete small quotient and its marked generation. -/
theorem PreparedChosenModule.raw_seven_source_partition
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (houtM : ¬K ≤ M)
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) K)
    (hb : IsAlternatingBlock K 7)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    let N := centralizer (Z1 : Set G) ⊓ Mc
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    ∃ p : Partition 7 4 ![2,2,2,1],
      let P := sevenPartitionPreimage K e p
      S ⊓ K ≤ P ∧ S ≤ normalizer (P : Set G) ∧
        generalizedFitting P = pCore 2 P ∧
        Nonempty (((P ⊔ S : Subgroup G) ⧸ pCore 2 (P ⊔ S : Subgroup G)) ≃* Perm (Fin 3)) ∧
        ¬IsAThreeProduct P ∧ P < K ∧ ¬P ≤ N ⊓ K ∧ P ⊔ (N ⊓ K) = K := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  have hn : S ≤ normalizer (K : Set G) := by
    apply h.raw_local_normalizes_of_oddRank hG T hZ hZne hK hi.quasisimple Nat.prime_three (by decide)
    rw [primeRank_equiv 3 e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 7 3 Nat.prime_three (by decide)]
  obtain ⟨p,hSP,hnP⟩ := sevenPartitionPreimage_normalized K S
    (T.isPGroup'.to_le inf_le_left) hn e
  obtain ⟨hf,⟨q⟩,hnot⟩ := sevenPartitionPreimage_intrinsic K hi.fitting e p
  exact ⟨p,hSP,hnP,hf,NormalSymmetricThreeExtension.normalized_join _ _ hnP q
    (T.isPGroup'.to_le inf_le_left),hnot,
    h.raw_seven_partition_generates hG T hM hJ hu hZ hK houtM hi hb e p⟩

end CFSG.Quasithin.Chapter15.Section01
