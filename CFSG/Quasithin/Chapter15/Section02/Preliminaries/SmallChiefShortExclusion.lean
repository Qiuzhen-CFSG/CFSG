module
public import CFSG.Quasithin.ChapterC.Section01.ShortChiefFactors
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveWreathExclusion.ComponentActions
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.FiveResidual

/-!
# Neither actual five-point rank-one factor is short

A short subnormal group moves at most one interval in a chief series of a
normal elementary subgroup. The two original H-chief factors both remain
moved on O²(H) in the single S₅ branch and on each actual C-component in
the S₅-wreath branch. Hence neither rank-one factor is short. This excludes
all natural block types, including orthogonal ones, without bounding or
eliminating their possible central fixed layers.

The pair application preserves the literal first factor Y₁Rc and the full
second parabolic H. The wreath application concerns the same K before the
quotient W/O₂(W); it does not assume that its chief factors survive that
quotient. Recognition and the final exclusions remain source obligations
of qt-e-152-small-parabolic.

Source: Aschbacher--Smith 15.2.4 and 15.2.8, printed pp.1105--1110;
C.1.7--8 and C.1.27, pp.123 and 133; F.1.12(I)(1),(2),(6), pp.262--263.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open NoncentralChiefRefinement ChapterB.QuasisimpleSource ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- Both original natural factors remain moved by the embedded O²(H).
The short-block support theorem excludes every short structure on this
literal residual, without any bound on its center or block dimension. -/
theorem ChosenSmallSource.symmetricFive_residual_not_short
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    let K := (pResidual 2 H).map H.subtype
    ¬ IsShort K := by
  classical
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let R := pResidual 2 H
  let K := R.map H.subtype
  dsimp only
  intro hshort
  have hR : IsBlock R := ⟨inferInstance,
    hshort.of_mulEquiv (equivMapOfInjective R H.subtype H.subtype_injective).symm,
    (inferInstance : R.Normal).isSubnormal⟩
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,j,hij,hs⟩ := h.symmetricFive_residual_chief_actions hprior hH he s
  have moved (k : Fin s.series.length) (hk : k ∈ ({i,j} : Finset (Fin s.series.length))) :
      ∃ r : R, ∃ v, s.factorRepresentation k (r : H) v ≠ v := by
    obtain ⟨_,_,_,_,hker,_,q,_,hq,hqk,_⟩ := hs k hk
    by_contra! hz
    have hqone (r : R) : q r = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [hqk,←hker,MonoidHom.mem_ker,actionHom_eq_one_iff]
      exact hz r
    obtain ⟨a,ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
    obtain ⟨r,rfl⟩ := hq a
    exact ha (hqone r)
  exact hij (hR.moved_factor_unique R s i j (moved i (by simp)) (moved j (by simp)))

/-- Both paired chief intervals are moved by each actual wreath component.
That component therefore cannot be short, before the passage to W/O₂(W). -/
theorem ChosenSmallSource.marked_five_wreath_component_not_short
    {T : Sylow 2 G} {M Mc V H K : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (hK : K ∈ Chapter1.cComponentsIn H) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
      DihedralMarking l 5 2 → ¬ IsShort K := by
  classical
  let := h.prepared.elementary
  intro l hd hshort
  let U := (conjugateSpan H V).subgroupOf H
  let R := K.subgroupOf H
  have hR : IsBlock R := ⟨inferInstance,
    hshort.of_mulEquiv (subgroupOfEquivOfLe hK.1).symm,hK.2.subnormal⟩
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,j,hij,hs⟩ := h.marked_five_wreath_component_chief_actions hH he hK l hd s
  have moved (k : Fin s.series.length) (hk : k ∈ ({i,j} : Finset (Fin s.series.length))) :
      ∃ r : R, ∃ v, s.factorRepresentation k (r : H) v ≠ v := by
    obtain ⟨_,_,_,_,_,_,_,_,_,hc⟩ := hs k hk
    by_contra! hz
    have hb : subspaceCommutator ((s.factorRepresentation k).comp R.subtype) ⊤ ⊤ = ⊥ :=
      (subspaceCommutator_eq_bot_iff _ _ _).mpr (fun v _ r => hz r v)
    rw [hb] at hc
    have hone : Nat.card (⊥ : Submodule (ZMod 2) (Additive (s.Factor k))) = 1 :=
      by simp
    omega
  exact hij (hR.moved_factor_unique R s i j (moved i (by simp)) (moved j (by simp)))

/-- The actual small-parabolic pair has a non-short rank-one factor O²(H).
The full second parabolic is still H, and the first is the literal Y₁Rc. -/
theorem SmallResidualWitness.symmetricFive_pair_not_short
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    let K := (pResidual 2 H).map H.subtype
    let L := ![Y₁ ⊔ (M ⊓ Mc).pCoreIn 2,K]
    ChapterF.Source.HypothesisF11 L (T : Subgroup G) ∧
      ChapterF.Source.parabolic L (T : Subgroup G) 1 = H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ IsShort K := by
  have hp := hw.symmetricFive_pair hH he
  exact ⟨hp.1,hp.2.2.1,hp.2.2.2.2.2,h.symmetricFive_residual_not_short hprior hH he⟩

end CFSG.Quasithin.Chapter15.Section02
