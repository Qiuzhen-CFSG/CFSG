module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.SingleComponent.Marking

/-!
# The specified critical match in the original single-component branch

The whole quotient action is constructed on the literal U/Z. Its paired
support coordinates produce the faithful component-automorphism marking,
and the selected critical-pair argument constructs the crossing for the
same suitable u. Its conjugator is x⁻¹ times the selected representative;
all subgroup labels are transported by that same element.

The genuine single-component and paired-support conclusions remain explicit
from 14.6.20--24(3). There is no selected-endpoint, rank-profile, coordinate,
embedding, fusion or crossing callback. The A₆ and two-component exclusions
and earlier support construction are still required for unconditional
14.6.24; qt-e-suitable-existence owns final suitable-choice assembly.

Source: Aschbacher--Smith, 14.6.24(4), printed p.1041.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.SelectedEndpoint
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The genuine single-component and paired-support inputs construct the
specified critical match for the original suitable element. The whole
quotient action, automorphism marking, embedding, exact kernel, fixed factor
and both commutator-coordinate profiles are constructed in the proof. -/
theorem source_crossing_of_single_component_supports
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
    (hK : (K.subgroupOf Mc).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL)
    (hKW : K ≤ normalizer (W : Set G))
    (s : G) (hs : s ∈ Mc) (hsW : W.map (MulAut.conj s).toMonoidHom = W')
    (u : G) (huW : u ∈ W)
    (hu : ComponentSupports.Suitable
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) Mc u) :
    let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let U := conjugateSpanBy (localModule T M) Mc
    ∃ i : h.CriticalEndpoint, ∃ x ∈ Mc, ∃ k : G,
      k = x⁻¹ * i.representative ∧
      (∀ A : Subgroup G, A.map (MulAut.conj k).toMonoidHom =
        (i.conjugate A).map (MulAut.conj x⁻¹).toMonoidHom) ∧
      ∃ q : SourceCrossingGeometry (localModule T M) Mc Mc u,
        q.A = U ∧ q.g = k ∧ ¬ centralizer ({u} : Set G) ≤ Mc := by
  dsimp only
  let hh := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let U := conjugateSpanBy (localModule T M) Mc
  let Z := centralInvolutions T
  let : IsElementaryAbelian 2 U :=
    hh.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans hh.UH_le_QH)
  let : (Z.subgroupOf U).Normal := inferInstance
  obtain ⟨ρ,d,_⟩ := BinaryConjugationSection.exists_descended_actor Mc U Z hh.UH_le_H
    (hh.point_lt.le.trans (le_conjugateSpanBy _ _)) (le_normalizer_conjugateSpanBy _ _)
    (hh.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    (QuotientGroup.mk' (pCore 2 Mc)) (QuotientGroup.mk'_surjective _) (by
      intro a ha b hb
      have hcore : (a:G) ∈ Mc.pCoreIn 2 :=
        mem_map_of_mem Mc.subtype ((QuotientGroup.eq_one_iff a).mp ha)
      have hc := hh.commutator_UH_QH_le_point (commutator_mem_commutator hb hcore)
      simpa only [commutatorElement_inv] using Z.inv_mem hc)
  let sec := TwoComponents.criticalSection hh d
  obtain ⟨ι,hι,emb,hi,he,hL⟩ := source_single_component_marking
    hG T hempty hM hunique hmany hcard e hab sec W W' f hf c cdual hWU hW'U hsep hB
    hpair K hKres hK eK hKW s hs hsW
  exact source_crossing_of_paired_sections
    hG T hempty hM hunique hmany hcard e hab sec ι hι emb hi he W W' hL f hf c cdual
    hWU hW'U hsep hB K hKres hK eK hKW s hs hsW u huW hu
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.SelectedEndpoint
