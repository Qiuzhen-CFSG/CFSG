module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerAxes
public import CFSG.Quasithin.Chapter10.SourceA5OriginalPairedOpposite
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveSections

/-!
# The original zero-center symmetric-five centralizer extension splits

The original paired core identifies the kernel of the factor centralizer
with the opposite block layer. The prescribed-conjugator axis theorem puts
that same layer on the opposite natural support. Its literal equivariant
natural section therefore supplies the faithful kernel marking for the
restricted S₅ quotient, whose splitting is already proved abstractly.

No involution lift, complement, or extra extension assumption is supplied.
The original quotient and the chosen paired product marking are retained.
Source: Aschbacher–Smith10.2.1, pp.742–743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false

/-- The original actual centralizer has a marked symmetric-five quotient and a group section. -/
@[expose] def SourceZeroCentralizerSymmetricSection : Prop :=
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  letI := (source_parabolic_module_reduced D).normal
  letI := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  let A := L.subgroupOf H
  let P := Y.comap q ⊓ centralizer (A : Set H)
  ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (α.comp Y.subtype),
    ∃ c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)),
    ∃ f : P →* Equiv.Perm (Fin 5), Function.Surjective f ∧
      f.ker = q.ker.subgroupOf P ∧
      ((∀ g : P, ∀ hg : q (g:H) ∈ Y, f g = (c.action.groupEquiv ⟨q (g:H),hg⟩).1) ∨
        (∀ g : P, ∀ hg : q (g:H) ∈ Y, f g = (c.action.groupEquiv ⟨q (g:H),hg⟩).2)) ∧
      ∃ σ : Equiv.Perm (Fin 5) →* P, f.comp σ = MonoidHom.id _

theorem source_a5_zero_centralizer_symmetric_section
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    SourceZeroCentralizerSymmetricSection D := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  have hU := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := L.subgroupOf H
  let P := Y.comap q ⊓ centralizer (A : Set H)
  obtain ⟨d,c,_,hN,haxis⟩ := source_a5_zero_original_centralizer_axes D e hn hout hz
  obtain ⟨t,ht,hne,hcomm,horbit,hsplit,hkA,hkB,hjoint⟩ :=
    source_a5_zero_centralizer_pair_centralizers D e hn hout hz
  let B := A.map (MulAut.conj t).toMonoidHom
  have hblockB : IsBlock B :=
    (source_a5_original_block_of_baumann_not_controlled D e hn hout).1.map_equiv (MulAut.conj t)
  have hu : U = pCore 2 H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (D.module_le_core.trans (pCoreIn_le 2 H))]
    exact source_a5_zero_centralizer_module_eq_core D e hn hout hz
  have hku : q.ker = U := hk.trans
    (source_a5_zero_centralizer_local_module_centralizer D e hn hout hz)
  have hK : q.ker ⊓ P = ⁅U,B⁆ := by
    change q.ker ⊓ (Y.comap q ⊓ centralizer (A : Set H)) = _
    rw [←inf_assoc,inf_eq_left.mpr (ker_le_comap q Y),hku,hu,hblockB.ambient_core_commutator]
    exact hkB
  have him : A.map q = (factorResidual q Y d.first).map q ∨
      A.map q = (factorResidual q Y d.second).map q :=
    haxis.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hop := paired_symmetric_commuting_conjugate_opposite U hU q hq hk d c A t hcomm him
  have hm (F : Subgroup H) (he : B.map q = F.map q) : (⁅U,B⁆ : Subgroup H) = ⁅U,F⁆ := by
    have he' : NormalElementaryQuotient.commutatorSpace U B =
        NormalElementaryQuotient.commutatorSpace U F := by
      rw [NormalElementaryQuotient.commutatorSpace_eq U q hq hk,
        NormalElementaryQuotient.commutatorSpace_eq U q hq hk,he]
    apply le_antisymm
    · intro x hx
      have hv : Additive.ofMul (⟨x,(commutator_le_left U B) hx⟩ : U) ∈
          NormalElementaryQuotient.commutatorSpace U B := hx
      rw [he'] at hv
      exact hv
    · intro x hx
      have hv : Additive.ofMul (⟨x,(commutator_le_left U F) hx⟩ : U) ∈
          NormalElementaryQuotient.commutatorSpace U F := hx
      rw [←he'] at hv
      exact hv
  rcases hop with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have hP : P.map q = d.second.map Y.subtype := by
      rcases haxis with h | h
      · exact h.2
      · have hc := paired_symmetric_first_residual_centralizer α q hq d c
        have hc' := paired_symmetric_second_residual_centralizer α q hq d c
        rw [←ha] at hc
        rw [←h.1] at hc'
        exact h.2.trans (hc'.symm.trans hc)
    obtain ⟨f,hf,hfk,hfc,σ,hσ⟩ := paired_second_axis_section U q hq hk d c P hP (hK.trans (hm _ hb))
    exact ⟨d,c,f,hf,hfk,Or.inr hfc,σ,hσ⟩
  · have hP : P.map q = d.first.map Y.subtype := by
      rcases haxis with h | h
      · have hc := paired_symmetric_first_residual_centralizer α q hq d c
        have hc' := paired_symmetric_second_residual_centralizer α q hq d c
        rw [←h.1] at hc
        rw [←ha] at hc'
        exact h.2.trans (hc.symm.trans hc')
      · exact h.2
    obtain ⟨f,hf,hfk,hfc,σ,hσ⟩ := paired_first_axis_section U q hq hk d c P hP (hK.trans (hm _ hb))
    exact ⟨d,c,f,hf,hfk,Or.inl hfc,σ,hσ⟩
end CFSG.Quasithin.Chapter10
