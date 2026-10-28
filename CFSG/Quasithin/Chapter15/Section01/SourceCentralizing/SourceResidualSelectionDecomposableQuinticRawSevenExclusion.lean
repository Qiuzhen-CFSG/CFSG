module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSevenPartition
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSevenOrdinary
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawParabolicPlacement
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticSeven
-- Only the record-free paired-A4 calculation is reused privately.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticSeven

/-! The original seven-letter normalizer row gives a literal three-pair
preimage placed in M intersection L. Its cubic residual centralizes V and
maps onto the paired A4. The full-block automorphism fixer bound is four,
contradicting the actual moving support image of order sixteen. All actions
are the proved support-to-Aut(L) actions; no reverse action is introduced. -/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open ChapterD ChapterD.UniqueFactor
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open AlternatingSeven.ThreeResidualLocals CaseIComponentData
variable {G : Type*} [Group G] [Finite G]

private theorem raw_seven_partition_image_false
    {M V L B : Subgroup G} (hb : IsAlternatingBlock L 7)
    (q : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (p : Partition 7 4 ![2,2,2,1])
    (hP : sevenPartitionPreimage L q p ≤ M ⊓ L)
    (hcubic : (primeToResidual 3 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ≤
      centralizer (V : Set G))
    (hBV : B ≤ V) (hn : B ≤ normalizer (L : Set G))
    (hcard : Nat.card (internalActionImage B L hn) = 16) : False := by
  let f := (alternatingGroup (Fin 7)).subtype.comp
    (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  let P := p.stabilizer.comap f
  let R := (primeToResidual 3 P).map P.subtype
  have hRV : R.map L.subtype ≤ centralizer (V : Set G) := by
    rw [show R = (primeToResidual 3 P).map P.subtype from rfl,
      map_embedded_primeToResidual_of_hom]
    exact (embedded_primeToResidual_mono 3 hP).trans
      hcubic
  have hf : f.range = alternatingGroup (Fin 7) := by
    apply le_antisymm
    · rintro g ⟨l,rfl⟩
      exact (q (QuotientGroup.mk' _ l)).property
    · intro g hg
      obtain ⟨l,hl⟩ := q.surjective.comp (QuotientGroup.mk'_surjective _) ⟨g,hg⟩
      exact ⟨l,congrArg Subtype.val hl⟩
  have hPf : P.map f = alternatingGroup (Fin 7) ⊓ p.stabilizer := by
    rw [show P = p.stabilizer.comap f from rfl,map_comap_eq,hf,inf_comm]
  obtain ⟨c,hc⟩ := p.three_pairs_stabilizer
  have hi : pairedFour.map (MulAut.conj c).toMonoidHom ≤ R.map f := by
    rw [show R = (primeToResidual 3 P).map P.subtype from rfl,
      map_embedded_primeToResidual_of_hom,hPf]
    exact CaseIComponentData.paired_le_partition_cubic_residual p c hc
  have hbound := hb.seven_paired_residual_fixer_card_le_four q R c hi
    (internalActionImage B L hn) (by
      rintro α ⟨b,rfl⟩ r hr
      apply Subtype.ext
      change (b : G) * (r : G) * (b : G)⁻¹ = r
      have hh := hRV (mem_map_of_mem L.subtype hr) b (hBV b.property)
      change (b : G) * (r : G) = (r : G) * (b : G) at hh
      rw [hh,mul_inv_cancel_right])
  rw [hcard] at hbound
  omega

/-- The same raw quintic component cannot have A7 as its original seed
normalizer image. The source parabolic is constructed and placed internally. -/
theorem PreparedChosenModule.raw_seven_normalizer_image_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L B : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (houtM : ¬L ≤ M)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    (hcubic : (primeToResidual 3 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ≤
      centralizer (V : Set G))
    (hBV : B ≤ V) (hn : B ≤ normalizer (L : Set G))
    (hcard : Nat.card (internalActionImage B L hn) = 16) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let R := S ⊓ normalizer (L : Set G)
    let H := L ⊔ R
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let q := QuotientGroup.mk' (centralizer (W : Set H))
    IsEmpty ((L.subgroupOf H).map q ≃* alternatingGroup (Fin 7)) := by
  constructor
  intro e
  obtain ⟨hb,t,_⟩ := h.raw_seven_ordinary_marked hG T hM hJ hu hZ hZne hL houtM hs hi e
  obtain ⟨p,_,hnP,hfit,hquot,hno,hPL,hout,_⟩ :=
    h.raw_seven_source_partition hG T hM hJ hu hZ hZne hL houtM hi hb t
  have hp := (h.raw_parabolic_placement_of_sylow_normalizes hG T hM hJ hu hZ hZne
    hs hL.1 hPL.le hnP hfit (Or.inl hquot) hno).resolve_right hout
  exact raw_seven_partition_image_false hb t p hp hcubic hBV hn hcard

end CFSG.Quasithin.Chapter15.Section01
