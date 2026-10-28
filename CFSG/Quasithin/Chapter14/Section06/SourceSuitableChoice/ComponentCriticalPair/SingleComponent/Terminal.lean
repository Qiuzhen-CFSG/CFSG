module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.SingleComponent.Crossing
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.ResidualCoordinates.Canonical
public import Theory.Representation.PSL3Two.NaturalDualMatrixSections

/-!
# Terminal assembly from the original single-component supports

The specified critical match, canonical fixed factor and seed, moving dual
eight-group, parabolic quotient and core/module bounds all use the same
suitable u and the same paired action. Their assembly constructs the
literal terminal witness required by the original suitable-choice argument.
The exchanger is inverted explicitly when passing to the residual-coordinate
convention.

The single-L₃(2) component and actual 14.6.20--23 supports remain explicit.
Thus this closes that terminal branch, not unconditional 14.6.24. The A₆ and
two-component source exclusions remain with qt-e-suitable-component-marking;
the support producer is qt-e-suitable-component-supports, and final
suitable-choice assembly belongs to qt-e-suitable-existence.

Source: Aschbacher--Smith, 14.6.22--24 and printed pp.1041--1042.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Finish the original terminal witness in the single-L3(2) branch from the
literal paired supports and the same suitable u. Every geometric record,
coordinate marking, critical match and numerical bound is constructed. -/
theorem source_terminal_witness_of_single_component_supports
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (W W' : Subgroup G)
    (f : (Mc ⊓ normalizer (W : Set G) : Subgroup G) →* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hf : Function.Surjective f)
    (c : BinaryConjugationSection (Mc ⊓ normalizer (W : Set G)) W (centralInvolutions T)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))
    (cdual : BinaryConjugationSection (Mc ⊓ normalizer (W : Set G)) W' (centralInvolutions T)
      (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f)))
    (hWU : W ≤ conjugateSpanBy (localModule T M) Mc)
    (hW'U : W' ≤ conjugateSpanBy (localModule T M) Mc)
    (hsep : W ⊓ W' ≤ centralInvolutions T)
    (hB : ⁅conjugateSpanBy (localModule T M) Mc,Mc⁆ ≤ W ⊔ W')
    (hpair : ∀ x ∈ Mc, W.map (MulAut.conj x).toMonoidHom = W ∨
      W.map (MulAut.conj x).toMonoidHom = W')
    (K : Subgroup G)
    (hKres : (solvableResidual Mc).map Mc.subtype = K)
    (hKtwo : (pResidual 2 Mc).map Mc.subtype = K)
    (hK : (K.subgroupOf Mc).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL)
    (hKW : K ≤ normalizer (W : Set G))
    (s : G) (hs : s ∈ (T : Subgroup G)) (hsW : W.map (MulAut.conj s).toMonoidHom = W')
    (u : G) (huW : u ∈ W)
    (hu : ComponentSupports.Suitable
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) Mc u) :
    SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  obtain ⟨i,x,hx,k,hk,hlabels,crossing,hcross⟩ :=
    SelectedEndpoint.source_crossing_of_single_component_supports
      hG T hempty hM hunique hmany hcard e hab W W' f hf c cdual hWU hW'U hsep hB hpair
      K hKres hK eK hKW s (h.T_le_H hs) hsW u huW hu
  have hswap : W'.map (MulAut.conj s⁻¹).toMonoidHom = W := by
    rw [←hsW,Subgroup.map_map]
    have he : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom = MonoidHom.id G := by
      apply MonoidHom.ext
      intro x
      simp only [MonoidHom.comp_apply,MonoidHom.id_apply,MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply,inv_inv]
      group
    rw [he,Subgroup.map_id]
  obtain ⟨⟨pa⟩,_,b,hb,t,ht,coords,hcoords⟩ := source_residual_geometry_of_paired_supports
    hG T hempty hM hunique hmany hcard e hab W W' hWU hW'U hsep hpair f hf c cdual hB
    K hKres hKtwo hK eK hKW s⁻¹ ((T : Subgroup G).inv_mem hs) hswap u huW hu
  let fSL := (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp f
  have hfSL : Function.Surjective fSL :=
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.surjective.comp hf
  obtain ⟨⟨n⟩,⟨d⟩⟩ := Matrix.PSL3Two.NaturalDualMarking.exists_matrix_pair f c cdual
  exact source_terminal_witness_of_natural_dual
    hG T hempty hM hunique hmany hcard e hab K W W' hKres hK eK hKW fSL hfSL n d
    hWU hW'U hsep u hu pa coords crossing
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
