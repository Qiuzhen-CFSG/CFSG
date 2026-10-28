module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.AlternatingSeven
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.AlternatingSeven.Partition

/-!
# The fixed plane centralizes the ordinary A₇ block module

The two-residual of the actual partition preimage is centralized by V₁.
Relabeling its partition identifies its image with the paired A₄. Its
permutation centralizer is the identity or a triple transposition, and the
original index-two bound rules out the latter. Aut(A₇)=S₇ aligns the
partition's quotient marking with the actual whole-module action, so the
trivial permutation image implies literal centralization of U(L).

This proves the module-centralization step of 15.1.25(5). The subsequent
full-cover centralizer control, A₆ residual, and cubic contradiction remain
local obligations of qt-e-1515-constrained-linear-quotient.
Source: Aschbacher--Smith 15.1.25(5), printed p.1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open AlternatingSeven.ThreeResidualLocals
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The fixed plane has trivial image in any natural action sharing the
quotient marking of the actual partition. -/
theorem ExchangedSource.a7_fixed_action_of_partition
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hTM : (T : Subgroup G) ≤ M)
    (q : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7))
    (p : Partition 7 4 ![2,2,2,1])
    (hplace : alternatingGroup (Fin 7) ⊓ p.stabilizer ≤
      ((M ⊓ d.L).subgroupOf d.L).map ((alternatingGroup (Fin 7)).subtype.comp
        (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L)))))
    (f : normalizer (d.L : Set G) →* Perm7)
    (hf : ∀ l : d.L, f ⟨l,d.L.le_normalizer l.property⟩ =
      (q (QuotientGroup.mk' (pCore 2 d.L) l)).val)
    (htriple : ∀ v ∈ d.nineFixedPlane, ∀ hv : v ∈ normalizer (d.L : Set G),
      (f ⟨v,hv⟩).cycleType ≠ {2,2,2}) :
    ∀ v ∈ d.nineFixedPlane, ∀ hv : v ∈ normalizer (d.L : Set G), f ⟨v,hv⟩ = 1 := by
  let fL := (alternatingGroup (Fin 7)).subtype.comp
    (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L)))
  let P := p.stabilizer.comap fL
  let R := (pResidual 2 P).map P.subtype
  have hP := s.a7_partition_preimage_le hTM q p fL rfl hplace
  have hfix := a7_partition_residual_fixed d P hP
  obtain ⟨c,hc⟩ := p.three_pairs_stabilizer
  have himage : R.map fL = pairedFour.map (MulAut.conj c).toMonoidHom := by
    have hh := a7_partition_residual_image d q p
    change R.map fL = _ at hh
    rw [conjugate_partition_twoResidual p.stabilizer c hc] at hh
    exact hh
  intro v hv hvL
  have hc : f ⟨v,hvL⟩ ∈ centralizer (pairedFour.map (MulAut.conj c).toMonoidHom : Set Perm7) := by
    intro g hg
    rw [←himage] at hg
    obtain ⟨l,hl,rfl⟩ := hg
    have hcomm : (l : G) * v = v * (l : G) :=
      hfix hv l (mem_map_of_mem d.L.subtype hl)
    have hh : (⟨l,d.L.le_normalizer l.property⟩ : normalizer (d.L : Set G)) * ⟨v,hvL⟩ =
        ⟨v,hvL⟩ * ⟨l,d.L.le_normalizer l.property⟩ := Subtype.ext hcomm
    have hm := congrArg f hh
    rw [map_mul,map_mul,hf] at hm
    exact hm
  rcases centralizer_conjugate_pairedFour _ c hc with he | he
  · exact he
  · exact False.elim (htriple v hv hvL he)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData


open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC BinaryPermutation.SevenNormalizer
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Choose the seven-letter action at a prescribed quotient marking. -/
theorem ExchangedSource.a7_action_at_quotient
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hb : IsAlternatingBlock d.L 7)
    (q : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7)) :
    ∃ f : normalizer (d.L : Set G) →* Equiv.Perm (Fin 7),
      (∀ l : d.L, f ⟨l,d.L.le_normalizer l.property⟩ =
        (q (QuotientGroup.mk' (pCore 2 d.L) l)).val) ∧
      (∀ v ∈ d.nineFixedPlane, ∀ hv : v ∈ normalizer (d.L : Set G),
        (f ⟨v,hv⟩).cycleType ≠ {2,2,2}) ∧
      ∀ (v : G) (hv : v ∈ normalizer (d.L : Set G)), f ⟨v,hv⟩ = 1 →
        v ∈ centralizer (((blockU d.L).map d.L.subtype) : Set G) := by
  obtain ⟨q0,E,f0,hq0,hE,htriple⟩ := s.constrained_a7_marked_action hb
  let a := q0.symm.trans q
  let c := permutationOfAut a
  let e := MulAut.conj c
  let f := e.toMonoidHom.comp f0
  have ha (x : alternatingGroup (Fin 7)) : (a x).val = e x.val := by
    exact (congrArg (fun b : MulAut (alternatingGroup (Fin 7)) => (b x).val)
      (conjugation_permutationOfAut a)).symm
  refine ⟨f,?_,?_,?_⟩
  · intro l
    change e (f0 _) = _
    rw [hq0,←ha]
    simp only [a,MulEquiv.trans_apply,q0.symm_apply_apply]
  · intro v hv hvL
    change (c * f0 ⟨v,hvL⟩ * c⁻¹).cycleType ≠ _
    rw [Equiv.Perm.cycleType_conj]
    exact htriple v hv hvL
  · intro v hvL hv
    have hf : f0 ⟨v,hvL⟩ = 1 := e.injective (hv.trans e.map_one.symm)
    intro u hu
    have hh := hE ⟨v,hvL⟩ ⟨u,hu⟩
    rw [hf,map_one,Module.End.one_apply,ofAdd_toAdd,E.symm_apply_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original index-two bound removes the triple transposition, so the
fixed plane centralizes the actual whole A₇ block module. -/
theorem ExchangedSource.constrained_a7_fixed_module
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V)
    (a : d.ConstrainedA7Alternative) :
    d.nineFixedPlane ≤ centralizer (((blockU d.L).map d.L.subtype) : Set G) := by
  obtain ⟨q,p,_,hp⟩ := a.partition
  obtain ⟨f,hf,htr,hker⟩ := s.a7_action_at_quotient a.block q
  have hn := s.constrained_a7_normalizes hG h a
  intro v hv
  have hvL : v ∈ normalizer (d.L : Set G) :=
    hn ((d.fixedPlane_le_sylow_cubicCentralizer hTM h hv).1)
  exact hker v hvL (s.a7_fixed_action_of_partition hTM q p hp f hf htr v hv hvL)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
