module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.Alternating
public import CFSG.Quasithin.ChapterC.Section06.Original.ModelOrbit
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.Source

/-!
# The original paired alternating-five C.5 family

The original block orbit constructs the two marked alternating setups,
its exchanging Sylow element, and its noncommuting conjugator. The core
centralizer identity then applies C.5.6(7)(iii) to the literal residual K
and Sylow subgroup R. This gives the full centralizer D=C_R(K), the core
product O₂(H)=O₂(K)D, and the two R-invariant maximum elementary abelian
subgroups, without assuming any of those marking data.

The characteristic-two branch of 14.6.9 consumes this theorem in
`SourceCharacteristicTwoBlocks.lean`. The later source argument proving
D=1 is separate.
Source: Aschbacher--Smith, C.5.6(7)(iii), printed pp.158--160,
and 14.6.9, printed pp.1025--1027 (refs/quasithin.pdf).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
open ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H M K R : Subgroup G}

/-- The actual paired A₅ orbit supplies all the markings of C.5.6(7)(iii). -/
theorem OriginalHypotheses.alternating_pair_family
    (c : OriginalHypotheses H M K R R)
    (b : OrbitDecomposition (c.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map H.subtype) 5)
    (hindex : R.relIndex M = 2) :
    ∃ x ∈ M, x ∉ R ∧
      let D := R ⊓ centralizer (K : Set G)
      let Q := H.pCoreIn 2
      (frattini D).map D.subtype = ⊥ ∧
      D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom = ⊥ ∧
      Q = K.pCoreIn 2 ⊔ D ∧
      Q ∈ elementaryAbelianMaxSubgroups R ∧
      ChapterB.baumann R = elementaryAbelianMaxJ R ∧
      {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} =
        {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom} := by
  let K₁ := (b.block i).map H.subtype
  let K₂ := (b.block j).map H.subtype
  obtain ⟨⟨h⟩,⟨h'⟩⟩ := c.alternating_paired_setups b i j hij hs hi
  have hjoin : K₁ ⊔ K₂ = K := c.pair_join b i j hij hs
  have hRK : R ≤ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    rw [hjoin]
    exact c.R_le_H.trans c.normalizes_residual
  have hH : H = (K₁ ⊔ K₂) ⊔ R := by rw [hjoin,c.residual_sup_sylow]
  have hno (W : Subgroup G) (hWR : W ≤ R) (hHW : H ≤ normalizer (W : Set G))
      (hMW : M ≤ normalizer (W : Set G)) : W = ⊥ :=
    c.no_common_normal W hWR ((normal_subgroupOf_iff_le_normalizer
      (hWR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hMW hHW))
  have hfull : R ⊓ centralizer ((sourceModule K₁ ⊔ sourceModule K₂ : Subgroup G) : Set G) =
      H.pCoreIn 2 := by
    simpa only [ambientModule_eq_literal,K₁,K₂,sourceModule,moduleLayer] using
      Section06.Original.pair_core_centralizer c b i j hij hs
  have hpair : ∀ r ∈ R, K₁.conjBy r = K₁ ∨ K₁.conjBy r = K₂ :=
    c.pair_action b i j hij hs
  obtain ⟨t,ht,_,he⟩ := c.pair_exchange b i j hij
  have ht' : ∃ t : M, (t : G) ∈ R ∧ K₁.conjBy (t : G) = K₂ :=
    ⟨⟨t,c.R_le_M ht⟩,ht,he⟩
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule K₁).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K₁ : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  have hd := h.fourModuleSourceInputs h'.module_le M R x hx (c.R_normal hx)
    hindex hpair ht' hnc
  have hfull' : R ⊓ centralizer ((sourceModule K₁ ⊔ sourceModule K₂ : Subgroup G) : Set G) =
      ((K₁ ⊔ K₂) ⊔ R).pCoreIn 2 := hfull.trans (congrArg (fun X : Subgroup G => X.pCoreIn 2) hH)
  have hp := h.source_C56_two_block_7 h' H M R le_rfl c.T_le c.R_normal hRK hH hno
    hfull' x hx hindex hpair ht' hnc
  have hf := h.two_block_invariant_family h' H M R le_rfl c.T_le c.R_normal hRK hH hno
    x hx hindex hpair ht' hnc
  dsimp only at hp hf
  have hD : ChapterB.baumann R ⊓ centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) =
      R ⊓ centralizer (K : Set G) := by rw [hp.2.2.2.1,hjoin]
  have hQ : ChapterB.baumann R ⊓ centralizer ((sourceModule K₁ ⊔ sourceModule K₂ : Subgroup G) : Set G) =
      H.pCoreIn 2 := by
    have ht := h.two_block_full_centralizer_eq h' H M R c.R_le_M c.T_le c.R_normal hRK hH hno
      x hx hindex hpair ht' hnc
    exact ht.1.symm.trans hfull
  dsimp only [K₁,K₂] at hD hH hjoin hQ
  refine ⟨x,hx,hd.x_outside,?_,?_,?_,?_,?_,?_⟩
  · exact hD ▸ hp.2.1
  · simpa only [hD] using hp.2.2.1
  · have hh := hp.2.2.2.2.1
    rw [←hH,hD,←hp.1,hjoin] at hh
    exact hh
  · simpa only [←hH] using hp.2.2.2.2.2.1
  · exact hf.2.1
  · simpa only [hQ] using hf.2.2.2

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
