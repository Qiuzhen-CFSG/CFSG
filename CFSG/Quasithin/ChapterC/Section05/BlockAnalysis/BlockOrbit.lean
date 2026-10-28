module

public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.Selection

/-!
# The transitive block product in C.5.3

A χ-block has at most two ambient conjugates in a characteristic-two SQTK
group. Its orbit under the original Sylow subgroup therefore has normal
span. If the block lies outside the unique maximal Sylow overgroup, that
span supplements the Sylow subgroup and is exactly the two-residual.
Enumerating the actual orbit retains the χ₀ type, J(R)-movement and the
literal transitive conjugation action.

Source: Aschbacher–Smith C.5.3, printed pp.154–155, using C.1.9 and C.1.29.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {A : Type*} [Group A] [Finite A]

/-- A moved source block outside the unique maximal overgroup generates
the entire residual under the supplied Sylow action. -/
theorem block_orbit_eq_residual
    (hf : generalizedFitting A = pCore 2 A) (hr : primeRank 3 A ≤ 2)
    (S : Sylow 2 A) (hu : Order.HasUniqueMaximalOver (S : Subgroup A) ⊤)
    (N : Subgroup A) (hN : (S : Subgroup A) ≤ N ∧ IsCoatom N)
    {L : Subgroup A} (hL : IsChiBlockIn L) (hout : ¬ L ≤ N) :
    conjugateSpanBy L (S : Subgroup A) = pResidual 2 A := by
  let V := conjugateSpanBy L (S : Subgroup A)
  let : V.Normal := conjugateSpanBy_sylow_normal L S
    (RankOne.ChiProduct.normal_or_index_two hf hr hL)
  have hv : V ⊔ (S : Subgroup A) = ⊤ := by
    by_contra hn
    exact hout ((le_conjugateSpanBy L (S : Subgroup A)).trans
      (le_sup_left.trans (hu.le_maximal ⟨hN.1,hN.2.covBy_top⟩ le_sup_right
        (lt_top_iff_ne_top.mpr hn))))
  apply le_antisymm
  · exact conjugateSpanBy_le (le_pResidual_of_isPPerfect L hL.1.short.twoPerfect)
      le_normalizer_of_normal
  · exact sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top V S S.isPGroup' hv⟩

/-- The actual Sylow orbit, before choosing its finite enumeration. -/
def BlockOrbit (S L : Subgroup A) :=
  {D : Subgroup A // ∃ s : S, D = L.map (MulAut.conj (s : A)).toMonoidHom}

omit [Finite A] in
instance (S L : Subgroup A) : Nonempty (BlockOrbit S L) :=
  ⟨⟨L.map (MulAut.conj (1 : A)).toMonoidHom,1,rfl⟩⟩

instance (S L : Subgroup A) : Finite (BlockOrbit S L) := by
  unfold BlockOrbit
  infer_instance

/-- Enumerated source blocks with all original subgroup placements retained. -/
structure OrbitDecomposition (S R K : Subgroup A) where
  size : ℕ
  positive : 0 < size
  size_le : size ≤ 2
  block : Fin size → Subgroup A
  injective : Function.Injective block
  type : ∀ i, IsChiZeroBlockIn (block i)
  generate : (⨆ i, block i) = K
  moved : ∀ i, block i = ⁅block i,elementaryAbelianMaxJ R⁆
  transitive : ∀ i j, ∃ s ∈ S,
    block j = (block i).map (MulAut.conj s⁻¹).toMonoidHom
  commute : Pairwise fun i j => block i ≤ centralizer (block j : Set A)
  permutes : ∀ s ∈ S, ∀ i, ∃ j,
    block j = (block i).map (MulAut.conj s).toMonoidHom

theorem orbitDecomposition_of_block
    (hf : generalizedFitting A = pCore 2 A) (hr : primeRank 3 A ≤ 2)
    (S R K : Subgroup A) (hSR : S ≤ normalizer (R : Set A))
    {L : Subgroup A} (hL : IsChiZeroBlockIn L)
    (hm : L = ⁅L,elementaryAbelianMaxJ R⁆)
    (hgen : conjugateSpanBy L S = K) : Nonempty (OrbitDecomposition S R K) := by
  classical
  let I := BlockOrbit S L
  let : Fintype I := Fintype.ofFinite I
  let n := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let D : Fin n → Subgroup A := fun i => (e.symm i).val
  have hd (i : Fin n) : IsChiZeroBlockIn (D i) := by
    obtain ⟨s,hs⟩ := (e.symm i).property
    rw [show D i = _ from hs]
    exact ⟨hL.1.map_equiv (MulAut.conj (s : A)),
      chiZero_equiv ((MulAut.conj (s : A)).subgroupMap L) hL.2⟩
  have hi : Function.Injective D := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hcard : n ≤ 2 := by
    have hh := (RankOne.ChiProduct.card_le_threeRank
      (RankOne.ChiProduct.blockCommutationHypothesis_of_fitting hf) D hi
      (fun i => (hd i).chi)).trans hr
    simpa only [Fintype.card_fin] using hh
  refine ⟨⟨n,Fintype.card_pos, hcard,D,hi,hd,?_,?_,?_,?_,?_⟩⟩
  · rw [←hgen,conjugateSpanBy_eq_iSup_conj]
    apply le_antisymm
    · apply iSup_le
      intro i
      obtain ⟨s,hs⟩ := (e.symm i).property
      rw [show D i = _ from hs]
      exact le_iSup (fun s : S => L.map (MulAut.conj (s : A)).toMonoidHom) s
    · apply iSup_le
      intro s
      let a : I := ⟨L.map (MulAut.conj (s : A)).toMonoidHom,s,rfl⟩
      have ha : D (e a) = L.map (MulAut.conj (s : A)).toMonoidHom := by
        dsimp only [D]; rw [e.symm_apply_apply]
      exact ha ▸ le_iSup D (e a)
  · intro i
    obtain ⟨s,hs⟩ := (e.symm i).property
    have hfix : (elementaryAbelianMaxJ R).map (MulAut.conj (s : A)).toMonoidHom =
        elementaryAbelianMaxJ R :=
      mem_normalizer_iff_map_conj_eq.mp
        (normalizer_le_normalizer_elementaryAbelianMaxJ R (hSR s.property))
    have he := congrArg (Subgroup.map (MulAut.conj (s : A)).toMonoidHom) hm
    rw [map_commutator,hfix] at he
    rw [show D i = _ from hs]
    exact he
  · intro i j
    obtain ⟨s,hs⟩ := (e.symm i).property
    obtain ⟨t,ht⟩ := (e.symm j).property
    refine ⟨(s : A) * (t : A)⁻¹,S.mul_mem s.property (S.inv_mem t.property),?_⟩
    rw [show D i = _ from hs,show D j = _ from ht,Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro a
    change (t : A) * a * (t : A)⁻¹ =
      ((s : A) * (t : A)⁻¹)⁻¹ * ((s : A) * a * (s : A)⁻¹) *
        (((s : A) * (t : A)⁻¹)⁻¹)⁻¹
    group
  · intro i j hij
    exact commutator_eq_bot_iff_le_centralizer.mp
      (blocks_commute (RankOne.ChiProduct.blockCommutationHypothesis_of_fitting hf)
        (hd i).1 (hd j).1 (fun he => hij (hi he)))
  · intro s hs i
    obtain ⟨t,ht⟩ := (e.symm i).property
    let B := (D i).map (MulAut.conj s).toMonoidHom
    have hB : ∃ a : S, B = L.map (MulAut.conj (a : A)).toMonoidHom := by
      refine ⟨⟨s * (t : A),S.mul_mem hs t.property⟩,?_⟩
      dsimp only [B]
      rw [show D i = _ from ht,Subgroup.map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change s * ((t : A) * x * (t : A)⁻¹) * s⁻¹ =
        (s * (t : A)) * x * (s * (t : A))⁻¹
      group
    let a : I := ⟨B,hB⟩
    refine ⟨e a,?_⟩
    change (e.symm (e a)).val = B
    rw [e.symm_apply_apply]

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
end
