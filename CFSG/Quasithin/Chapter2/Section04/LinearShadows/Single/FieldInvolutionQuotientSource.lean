module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CyclicSource
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.GroupTheory.NormalQuotientOuterAction

/-!
# The actual field involution on the block quotient

The original Hall-torus complement misses the block. Since the kernel of its
quotient action lies in the absorbed two-core, a nonidentity complement actor
is outer on L/O₂(L). An involution is therefore an inner conjugate of the
half-degree Frobenius, and its fixed quotient is the corresponding smaller
PSL₂. The actor and quotient maps are the literal source maps.

Source: Aschbacher–Smith, Lemma 2.4.12(2), printed p.532.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_field_actor_not_inner
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (f : ((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G) : Subgroup G))
    (hf : f ≠ 1) :
    let : d.block.Normal := hsingle ▸ d.L0_normal
    let fH : d.H := inclusion (inf_le_left.trans (map_subtype_le _)) f
    normalQuotientAction d.block (pCore 2 d.block) fH ∉
      MulAut.innerSubgroup (d.block ⧸ pCore 2 d.block) := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let fH : d.H := inclusion (inf_le_left.trans (map_subtype_le _)) f
  have hQL : pCore 2 d.H ≤ d.block := by
    intro a ha
    have hcore := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).2
    have ha' : (a:G) ∈ (d.block.map d.H.subtype).pCoreIn 2 := by
      change (a:G) ∈ twoCore (d.block.map d.H.subtype)
      rw [hcore]
      exact mem_map_of_mem d.H.subtype ha
    exact (mem_map_iff_mem d.H.subtype_injective).mp (pCoreIn_le 2 _ ha')
  change normalQuotientAction d.block (pCore 2 d.block) fH ∉
    MulAut.innerSubgroup (d.block ⧸ pCore 2 d.block)
  intro hi
  have hm : fH ∈ (MulAut.innerSubgroup (d.block ⧸ pCore 2 d.block)).comap
      (normalQuotientAction d.block (pCore 2 d.block)) := hi
  rw [normalQuotientAction_comap_inner, sup_eq_left.mpr
    ((source_block_quotient_action_kernel d hsingle hL).trans hQL)] at hm
  have hfL : (f:G) ∈ d.block.map d.H.subtype := mem_map_of_mem d.H.subtype hm
  have hd := (source_torus_normalizer_complements_of_choice d hG T hST hsingle hL
    hM hTM hunique c.hall c.split_ambient).2.2.2.1
  exact hf (Subtype.ext (disjoint_def.mp hd hfL f.property))

private theorem quotient_binary_equiv {L : Type*} [Group L] {n : ℕ}
    (hL : ChapterC.IsL2EvenBlock L n) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Theory.PSL2.BinaryGroup n) := by
  obtain ⟨_,_,F,_,_,hF,_,r,⟨m⟩,hm⟩ := hL
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (Theory.PSL2.BinaryField n) := Fintype.ofFinite _
  let e : F ≃+* Theory.PSL2.BinaryField n := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF,
      GaloisField.card 2 n (by omega)])
  exact ⟨(m.quotientIso.trans (Atlas.fieldEquivSL 2 e)).trans
    (Theory.PSL2.sl2QuotientEquiv _)⟩

theorem source_field_involution_quotient_fixed_model
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (f : ((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G) : Subgroup G))
    (hf : orderOf f = 2) :
    let : d.block.Normal := hsingle ▸ d.L0_normal
    let fH : d.H := inclusion (inf_le_left.trans (map_subtype_le _)) f
    let α := normalQuotientAction d.block (pCore 2 d.block) fH
    ∃ m : ℕ, 0 < m ∧ n = 2*m ∧
      Nonempty (α.fixedSubgroup ≃* Theory.PSL2.BinaryGroup m) := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let fH : d.H := inclusion (inf_le_left.trans (map_subtype_le _)) f
  let α := normalQuotientAction d.block (pCore 2 d.block) fH
  change ∃ m : ℕ, 0 < m ∧ n = 2*m ∧
    Nonempty (α.fixedSubgroup ≃* Theory.PSL2.BinaryGroup m)
  have hn2 : 2 ≤ n := hL.1
  obtain ⟨e⟩ := quotient_binary_equiv hL
  let a := MulAut.congr e α
  have hf2 : f ^ 2 = 1 := by simpa only [hf] using pow_orderOf_eq_one f
  have hα2 : α ^ 2 = 1 := by
    change normalQuotientAction d.block (pCore 2 d.block) fH ^ 2 = 1
    rw [← map_pow]
    have hh : fH ^ 2 = 1 := congrArg
      (inclusion (show ((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G) : Subgroup G) ≤ d.H
        from inf_le_left.trans (map_subtype_le _))) hf2
    rw [hh, map_one]
  have ha2 : a ^ 2 = 1 := by dsimp only [a]; rw [← map_pow, hα2, map_one]
  have houter : ¬ ∃ b : Theory.PSL2.BinaryGroup n, a = MulAut.conj b := by
    rintro ⟨b,hb⟩
    have ha : a ∈ (MulAut.innerSubgroup (d.block ⧸ pCore 2 d.block)).map
        (MulAut.congr e).toMonoidHom := by
      rw [MulAut.map_innerSubgroup_congr]
      exact ⟨b,hb.symm⟩
    obtain ⟨a',ha',he⟩ := ha
    have he' : a' = α := (MulAut.congr e).injective he
    exact source_field_actor_not_inner d hG T hST hsingle hL hM hTM hunique c f
      (by intro h; simp [h] at hf) (show α ∈ MulAut.innerSubgroup _ from he' ▸ ha')
  obtain ⟨g,σ,hsem⟩ := Theory.PSL2.semilinear_coverage a
  obtain ⟨m,hm,hn,⟨j⟩⟩ := Theory.PSL2.outer_fixed_model_of_semilinear
    (by omega : 2 ≤ n) a ha2 g σ hsem houter
  exact ⟨m,hm,hn,⟨(MulAut.fixedSubgroupCongr e α).trans j⟩⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
