module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Contracts
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiTransport
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The original E.6.7 block product and Thompson movement

Apply the proved known-simple local C(G,T) theorem inside the original
intermediate characteristic-two subgroup. Taking the family of all moved
chi-zero blocks outside its intersection with M makes its indexing injective.
The block commutation theorem and the actual three-rank bound give at most
two factors. The source ordered product supplies the literal set product.
Every factor and Thompson subgroup is then mapped by the original inclusion.

This proves E.6.7(1). The Borel identifications and the V-action calculations
needed for clauses (2),(3) are separate parts of the full source assembly.
Source: Aschbacher–Smith E.6.7, printed p.246, using C.1.29, printed p.134.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
open ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The complete first clause, retaining the literal product, original
Thompson movement, and escape of every selected factor from M. -/
structure SourceFamily (Q M H : Subgroup G) extends BlockFamily H M where
  product : (H : Set G) = ((H ⊓ M : Subgroup G) : Set G) *
    ((⨆ i, block i : Subgroup G) : Set G)
  thompson : ∀ i, block i = ⁅block i, elementaryAbelianMaxJ Q⁆
  outside : ∀ i, ¬ block i ≤ M

/-- E.6.7(1) on the actual intermediate subgroup, with all earlier
classification inputs discharged for the full known-simple catalogue. -/
theorem sourceFamily_knownSimple
    {T : Sylow 2 G} {M V W H : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hW : W ∈ obstructionFamily M V)
    (hQH : sylowCentralizer (T : Subgroup G) V ≤ H)
    (hHC : H ≤ centralizer (W : Set G)) (hc : HasCharacteristicTwo H) :
    Nonempty (SourceFamily (sylowCentralizer (T : Subgroup G) V) M H) := by
  classical
  let Q := sylowCentralizer (T : Subgroup G) V
  let N := M.subgroupOf H
  obtain ⟨S, hS⟩ := h.sylow_obstructionIntermediate hW hQH hHC
  have hSH : (S : Subgroup H) = Q.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le hQH]
  have hf : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 hc
  have hsq := h.obstructionIntermediate_sqtk hW hHC
  have hcontrol : (S : Subgroup H).characteristicNormalizerClosure ≤ N := by
    rw [hSH]
    exact h.characteristic_normalizers_intermediate hQH
  obtain ⟨r₀, _hr₀, L₀, ht₀, ho₀, hm₀, hp₀⟩ :=
    RankOne.ChiProduct.SelectedRankOne.ordered_chiZero_product_knownSimple
      hsq hf S N hcontrol
  let I := {L : Subgroup H // IsChiZeroBlockIn L ∧
    L = ⁅L, elementaryAbelianMaxJ (S : Subgroup H)⁆ ∧ ¬ L ≤ N}
  let : Fintype I := Fintype.ofFinite I
  let r := Fintype.card I
  let e : I ≃ Fin r := Fintype.equivFin I
  let L : Fin r → Subgroup H := fun i => (e.symm i).val
  let B : Fin r → Subgroup G := fun i => (L i).map H.subtype
  have ht (i) : IsChiZeroBlockIn (L i) := (e.symm i).property.1
  have hm (i) : L i = ⁅L i, elementaryAbelianMaxJ (S : Subgroup H)⁆ :=
    (e.symm i).property.2.1
  have ho (i) : ¬ L i ≤ N := (e.symm i).property.2.2
  have hi : Function.Injective L := fun i j he => e.symm.injective (Subtype.ext he)
  have hguard := RankOne.ChiProduct.blockCommutationHypothesis_of_fitting hf
  have hr : r ≤ 2 := by
    have hh := (RankOne.ChiProduct.card_le_threeRank hguard L hi
      (fun i => (ht i).chi)).trans (hsq.stronglyQuasithin 3 Nat.prime_three (by decide))
    simpa only [Fintype.card_fin] using hh
  have hBL (i) : B i ≤ H := map_subtype_le _
  have hjoin : (⨆ i, L i).map H.subtype = ⨆ i, B i := map_iSup _ _
  have hmem (i : Fin r₀) : L₀ i ≤ ⨆ j, L j := by
    let b : I := ⟨L₀ i, ht₀ i, hm₀ i, ho₀ i⟩
    have hb : L (e b) = L₀ i := by dsimp only [L]; rw [e.symm_apply_apply]
    exact hb ▸ le_iSup L (e b)
  have hprod : (H : Set G) = ((H ⊓ M : Subgroup G) : Set G) *
      ((⨆ i, B i : Subgroup G) : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, b, hb⟩ := hp₀ ⟨x, hx⟩
      let z : H := (List.ofFn (fun i => (b i : H))).prod
      have hz : z ∈ ⨆ i, L i := by
        apply Subgroup.list_prod_mem
        intro a ha
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
        exact hmem i (b i).property
      have hzG : (z : G) ∈ ⨆ i, B i := by
        rw [← hjoin]
        exact mem_map_of_mem H.subtype hz
      exact Set.mem_mul.mpr ⟨((m : H) : G), ⟨(m : H).property, m.property⟩,
        (z : G), hzG, (congrArg H.subtype hb).symm⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact H.mul_mem ha.1 ((iSup_le hBL) hb)
  refine ⟨{ count := r
            count_le_two := hr
            block := B
            le := hBL
            type := ?_
            subnormal := ?_
            commuting := ?_
            generated := ?_
            product := hprod
            thompson := ?_
            outside := ?_ }⟩
  · intro i
    exact (ht i).2.of_mulEquiv ((L i).equivMapOfInjective H.subtype H.subtype_injective)
  · intro i
    simpa only [B, Subgroup.subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
      using (ht i).1.subnormal
  · intro i j hij
    apply commutator_eq_bot_iff_le_centralizer.mp
    change ⁅(L j).map H.subtype, (L i).map H.subtype⁆ = ⊥
    rw [← map_commutator,
      blocks_commute hguard (ht j).1 (ht i).1 (fun he => hij (hi he).symm), Subgroup.map_bot]
  · apply le_antisymm
    · intro x hx
      have hxset : x ∈ (H : Set G) := hx
      rw [hprod] at hxset
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hxset
      exact mul_mem_sup ha hb
    · exact sup_le inf_le_left (iSup_le hBL)
  · intro i
    change (L i).map H.subtype = ⁅(L i).map H.subtype, elementaryAbelianMaxJ Q⁆
    change (S : Subgroup H).map H.subtype = Q at hS
    rw [← hS, elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      ← map_commutator, ← hm]
  · intro i hle
    apply ho i
    intro x hx
    exact hle (mem_map_of_mem H.subtype hx)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
