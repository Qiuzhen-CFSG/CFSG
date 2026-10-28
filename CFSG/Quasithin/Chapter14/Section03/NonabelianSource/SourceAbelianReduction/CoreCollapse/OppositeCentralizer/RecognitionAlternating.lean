module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionOddCore
public import Theory.GroupTheory.CyclicSL23CubicConjugates
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FixedFour
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# Eliminating the alternating rows of the opposite-centralizer catalogue

For the original involution z, any fixed A₄ in a component lies in O²(H):
A₄ is two-perfect and its image centralizes z. The marked local residual
centralizer is C₄ ∗ SL₂(3), which has no A₄ subgroup. A cubic element of this
central product cannot move an element to a distinct commuting conjugate,
whereas the cubic action on the Klein four subgroup of A₄ does so.

Both alternating actions in 1.1.5(3) have a fixed A₄. The odd-core reduction
already excludes their triple covers, so neither alternating row occurs.
Consequently the remaining original-point component actions are inner.
The quotient recognition and core-collapse assembly remain with the owner
of the original 14.3.22 argument.

Source: Aschbacher--Smith, 14.3.22, printed p.999, inspection of the marked
C₄ ∗ SL₂(3) centralizer after applying 1.1.5(3).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)
private theorem model_fixedFour_transport {D : Type*} [Group D] {α : MulAut D}
    {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (e : D ≃* alternatingGroup (Fin n))
    (he : ∀ x, (e (α x) : Equiv.Perm (Fin n)) = σ * e x * σ⁻¹)
    (f : alternatingGroup (Fin 4) →* alternatingGroup (Fin n))
    (hf : Function.Injective f)
    (hfix : ∀ x, σ * (f x : Equiv.Perm (Fin n)) * σ⁻¹ = f x) :
    ∃ j : alternatingGroup (Fin 4) →* D, Function.Injective j ∧ ∀ x, α (j x) = j x := by
  refine ⟨e.symm.toMonoidHom.comp f, e.symm.injective.comp hf, ?_⟩
  intro x
  apply e.injective
  apply Subtype.ext
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply] using (he (e.symm (f x))).trans (by simpa using hfix x)


include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs hc s


theorem source_triple_no_fixed_alternatingFour
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))} {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (f : alternatingGroup (Fin 4) →* D) (hf : Function.Injective f)
    (hfix : ∀ x, α (f x) = f x) : False := by
  let C := ResidualFusion.C (tripleProduct d a)
  have hlocal := source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨E,B,⟨eE⟩,⟨eB⟩,hEB,_,hjoin⟩ := hlocal.residual_centralizer
  have hfH (x : alternatingGroup (Fin 4)) : (f x : G) ∈ F.H := by
    rw [F.H_eq_centralizer (by decide) z s.point]
    apply mem_centralizer_singleton_iff.mpr
    have hh := hα (f x)
    rw [hfix] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  let k : alternatingGroup (Fin 4) →* F.H :=
    { toFun := fun x => ⟨(f x : G), hfH x⟩
      map_one' := by simp only [map_one]; rfl
      map_mul' := by intros; simp only [map_mul]; rfl }
  have hp : IsPPerfect 2 (alternatingGroup (Fin 4)) := by
    rw [←Equiv.Perm.twoResidual_eq_alternating]
    exact isPPerfect_pResidual 2
  have hk : k.range ≤ pResidual 2 F.H := by
    have hh := map_pResidual_le 2 k
    rwa [(pResidual_eq_top_iff 2 _).mpr hp, ←MonoidHom.range_eq_map] at hh
  let j : alternatingGroup (Fin 4) →* G := C.subtype.comp (D.subtype.comp f)
  have hj : Function.Injective j := C.subtype_injective.comp (D.subtype_injective.comp hf)
  have hE : ∀ u ∈ E, u^4=1 := by
    intro u hu
    have hh : (⟨u,hu⟩ : E)^4 = 1 := by
      apply eE.injective
      rw [map_pow,map_one]
      simpa using pow_card_eq_one' (x := eE ⟨u,hu⟩)
    exact congrArg Subtype.val hh
  apply no_alternatingFour_embedding_cyclic_sl23 E B hE eB hEB j hj
  rintro _ ⟨x,rfl⟩
  rw [hjoin]
  refine ⟨mem_map.mpr ⟨k x,hk ⟨x,rfl⟩,rfl⟩, ?_⟩
  exact ((f x : D) : C).property


theorem source_triple_not_alternatingSix
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (σ : Equiv.Perm (Fin 6)) (hσ : σ.IsSwap) : ¬AlternatingAction α 6 σ := by
  intro ha
  obtain ⟨eA,heA⟩ := source_triple_alternating_action_model
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD ha
  obtain ⟨f,hf,hfix⟩ := AlternatingSix.ShadowLocal.swap_fixed_alternatingFour_embedding σ hσ
  obtain ⟨j,hj,hjfix⟩ := model_fixedFour_transport eA heA f hf hfix
  exact source_triple_no_fixed_alternatingFour
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hα j hj hjfix

theorem source_triple_not_alternatingSeven
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    {α : MulAut D}
    (hα : ∀ x : D, ((α x : ResidualFusion.C (tripleProduct d a)) : G) = z * (x : G) * z⁻¹)
    (σ : Equiv.Perm (Fin 7)) (hσ : σ.cycleType = {2,2,2}) : ¬AlternatingAction α 7 σ := by
  intro ha
  obtain ⟨eA,heA⟩ := source_triple_alternating_action_model
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD ha
  obtain ⟨f,hf,hfix⟩ := AlternatingSix.ShadowLocal.tripleSwapSeven_fixed_alternatingFour_embedding σ hσ
  obtain ⟨j,hj,hjfix⟩ := model_fixedFour_transport eA heA f hf hfix
  exact source_triple_no_fixed_alternatingFour
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hα j hj hjfix

theorem source_triple_inner_marked_component
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    let C := ResidualFusion.C (tripleProduct d a)
    ∃ (D : Subgroup C) (α : MulAut D) (P : Sylow 2 D),
      IsComponent C D ∧
      (∀ x : D, ((α x : C) : G) = z * (x : G) * z⁻¹) ∧
      Chapter1.SmallTwoPart.SmallModelAction115 D α ∧
      α ∈ (MulAut.conj (G := D)).range ∧ orderOf α = 2 ∧
      Nat.card P ∣ 128 ∧ (∀ x : P, α (x : D) = x) ∧
      Nat.card α.fixedSubgroup ∣ 384 ∧ ¬128 ∣ Nat.card (D ⧸ pCore 2 D) := by
  intro C
  obtain ⟨D,α,P,hD,hα,hm,ho,hP,hfix,hfc,hsmall⟩ := source_triple_small_marked_component
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hi : α ∈ (MulAut.conj (G := D)).range := by
    cases hm with
    | lie _ _ hi => exact hi
    | two_cover _ _ _ hi => exact hi
    | six σ hσ ha => exact (source_triple_not_alternatingSix
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hα σ hσ ha).elim
    | seven σ hσ ha => exact (source_triple_not_alternatingSeven
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD hα σ hσ ha).elim
    | odd _ hi => exact hi
    | sporadic _ _ _ ha => exact ha.1
  exact ⟨D,α,P,hD,hα,hm,hi,ho,hP,hfix,hfc,hsmall⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
