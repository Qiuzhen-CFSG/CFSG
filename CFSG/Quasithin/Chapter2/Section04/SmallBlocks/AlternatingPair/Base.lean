module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.IndexTwo
public import Theory.GroupTheory.PairNormalizerIndex

/-! The literal half-Sylow base and proper intersection with M in source
2.4.25. The pair action gives index two. The already proved original core
is maximum elementary, so it lies in this stabilizer and the original
beta criterion applies. Both blocks remain outside M. -/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G}
  {d : MinimalBlockSetup M}

omit [Finite G] in
theorem AlternatingPairSourceSetup.second_not_le_M
    (c : AlternatingPairSourceSetup d M₀) : ¬ c.second ≤ M := by
  obtain ⟨t,ht,he⟩ := c.exchange
  change (d.block.map d.H.subtype).map (MulAut.conj t).toMonoidHom = c.second at he
  have hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M := d.full_pair.1.1.2.1
  intro hL
  apply d.outside
  intro l hl
  have hh := hL (he ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hl)
  have hv : t⁻¹ * (t*l*t⁻¹) * t ∈ M := M.mul_mem (M.mul_mem (M.inv_mem (hSM ht)) hh) (hSM ht)
  simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hv

/-- The original block stabilizer is an admissible half-Sylow local base. -/
theorem AlternatingPairSourceSetup.stabilizer_base
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let SI := S ⊓ normalizer (d.block.map d.H.subtype : Set G)
    SI.relIndex S = 2 ∧ elementaryAbelianMaxJ S ≤ SI ∧
      twoCore d.H ≤ SI ∧ SI ∈ beta M := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let SI := S ⊓ normalizer (L : Set G)
  have hhalf : SI.relIndex S = 2 := by
    obtain ⟨t,ht,he⟩ := c.exchange
    change L.map (MulAut.conj t).toMonoidHom = c.second at he
    simpa only [SI,inf_relIndex_left] using normalizer_relIndex_eq_two_of_pair S L c.second
      c.permutes t ht (by rw [he]; exact c.second_ne)
  have hJS₀ : elementaryAbelianMaxJ S ≤ S := sSup_le (fun _ hA => hA.1)
  have hJB : elementaryAbelianMaxJ S ≤ ChapterB.baumann S := by
    refine le_inf hJS₀ ?_
    intro j hj w hw
    obtain ⟨wJ,hwJ,rfl⟩ := hw
    obtain ⟨wZ,_,rfl⟩ := hwJ
    exact congrArg Subtype.val ((mem_center_iff.mp wZ.property) ⟨j,hj⟩).symm
  have hJS : elementaryAbelianMaxJ S ≤ SI :=
    le_inf hJS₀ (hJB.trans c.marked₁.normalizes)
  have hcore := (d.lemma_2_4_5_2a_4 hG T hST M₀ hSM hMT hi).2.2
  have hQJ : twoCore d.H ≤ elementaryAbelianMaxJ S := le_sSup hcore
  have hQS := hQJ.trans hJS
  refine ⟨hhalf,hJS,hQS,?_⟩
  exact lemma_2_3_8_5b hG T hM hTM hu d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl
    hJS inf_le_left hhalf
    (lemma_2_3_8_5c d.mem_gammaEvenZero.1 d.mem_gammaEvenZero.2 d.full_pair d.S le_rfl hQS).2
end CFSG.Quasithin.Chapter2
