module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleCoordinates
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.NormalLayerSource
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import Theory.Representation.BinaryOffender.AlternatingFiveQuotient
/-!
# The original quasisimple symmetric-five moved-section marker

The original B.5.1 section gives the natural A₅ quotient of [U,O²(G)].
The natural normalizer theorem extends this to the whole faithful S₅
quotient, preserving its kernel and the original equivariant projection.
This proof is shared by the C.1.26 block selection and E.2.3 consumers.

Source: Aschbacher–Smith B.6.9, C.1.26 and E.2.3, pp.115–116,132,217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {B A : Subgroup D}
private noncomputable def markedFiveRestriction
    (e : MarkedActionEquiv ρ B A (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5))) :
    ActionEquiv (ρ.comp A.subtype)
      ((BinaryPermutation.naturalRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype) where
  groupEquiv := e.subgroupEquiv
  linearEquiv := e.action.linearEquiv
  intertwines a v := by
    have hh := e.action.intertwines ⟨a,e.contained a.property⟩ v
    rw [e.compatible] at hh
    exact hh

private theorem markedFive_proper
    (e : MarkedActionEquiv ρ B A (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5))) : A ≠ ⊤ := by
  intro he
  let b := e.action.groupEquiv.symm (Equiv.swap 0 1)
  let a : A := ⟨(b:D),he ▸ mem_top _⟩
  have hb : (⟨(a:D),e.contained a.property⟩ : B) = b := Subtype.ext rfl
  have hc := e.compatible a
  rw [hb] at hc
  change e.action.groupEquiv (e.action.groupEquiv.symm (Equiv.swap 0 1)) = _ at hc
  rw [e.action.groupEquiv.apply_symm_apply] at hc
  have hm : Equiv.swap (0:Fin 5) 1 ∈ alternatingGroup (Fin 5) :=
    hc.symm ▸ (e.subgroupEquiv a).property
  norm_num [Equiv.Perm.mem_alternatingGroup] at hm

variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

theorem quasisimple_five_source_marker
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    let W := ⁅U,pResidual 2 G⁆
    ∃ p : G →* Equiv.Perm (Fin 5), ∃ hp : Function.Surjective p,
      ∃ hk : p.ker = centralizer (W:Set G),
      ∃ f : Additive W →ₗ[ZMod 2] BinaryPermutation.core (Fin 5),
      Function.Surjective f ∧
      (∀ g v, f (NormalElementaryQuotient.representation W p hp hk g v) =
        BinaryPermutation.coreRepresentation (Fin 5) g (f v)) ∧
      f.ker = fixedSpace (NormalElementaryQuotient.representation W p hp hk)
        ((pResidual 2 G).map p) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let A := generalizedFitting Y
  let W := ⁅U,pResidual 2 G⁆
  let := offenderSubgroup_normal α
  have hcore : pCore 2 H = ⊥ := by
    let i := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 i,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  have hL := (source_quasisimple_fitting_eq_residual (T.mapSurjective hq) hp Y
    (offender_generation (T.mapSurjective hq) hp α hff hcore).2 hqs).1
  have hX : A.map Y.subtype = (pResidual 2 G).map q := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact hL
  let L := A.map Y.subtype
  let : L.Normal := by change (A.map Y.subtype).Normal; infer_instance
  have hself : centralizer (L:Set H) ≤ L := by
    change centralizer (A.map Y.subtype:Set H) ≤ A.map Y.subtype
    rw [hL]
    exact centralizer_pResidual_le_of_pCore_eq_bot hcore
  have hproper : L ≠ ⊤ := by
    intro ht
    apply markedFive_proper e
    apply top_unique
    intro y _
    have hy : (y:H) ∈ L := ht ▸ mem_top _
    obtain ⟨a,ha,he⟩ := hy
    exact (Y.subtype_injective he) ▸ ha
  let hkerW := hker.trans (hU.centralizer_moved_eq U).symm
  let β := NormalElementaryQuotient.representation W q hq hkerW
  let eA := markedFiveRestriction e
  let f := sourceMovedQuotientMap U q hq hker Y A s (pResidual 2 G) hX _ eA
  have hf : Function.Surjective f :=
    sourceMovedQuotientMap_surjective U q hq hker Y A s (pResidual 2 G) hX _ eA
  have hfk : f.ker = fixedSpace β L := by
    ext v
    rw [show L = (pResidual 2 G).map q from hX,NormalElementaryQuotient.mem_fixedSpace_image]
    exact sourceMovedQuotientMap_kernel U q hq hker Y A s (pResidual 2 G) hX _ eA v
  let eg := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans e.subgroupEquiv
  have hfe : ∀ (g:L) v, f (β (g:H) v) =
      BinaryPermutation.naturalRepresentation (Fin 5) (eg g) (f v) := by
    intro g v
    obtain ⟨x,hx⟩ := hq (g:H)
    let a := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm g
    have ha : q x = (a:Y) := hx.trans ((congrArg Subtype.val
      ((A.equivMapOfInjective Y.subtype Y.subtype_injective).apply_symm_apply g)).symm)
    have hv : β (g:H) v = Additive.ofMul (MulAut.conjNormal x v.toMul) := by
      rw [← hx]
      apply Additive.toMul.injective
      apply Subtype.ext
      exact NormalElementaryQuotient.representation_apply W q hq hkerW x v
    rw [hv]
    exact sourceMovedQuotientMap_conjugation U q hq hker Y A s (pResidual 2 G) hX _ eA x a ha v
  obtain ⟨j,hj,hfj,hjL⟩ := exists_five_quotient_of_natural_layer β L hself hproper eg f hf hfk hfe
  let p := j.comp q
  have hp : Function.Surjective p := hj.2.comp hq
  have hpk : p.ker = centralizer (W:Set G) := by
    change (j.comp q).ker = _
    rw [MonoidHom.ker_comp_of_injective q j hj.1,hkerW]
  let c := (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)).symm
  let f' := c.toLinearMap.comp f
  have hf' : Function.Surjective f' := c.surjective.comp hf
  have hfull : ∀ g v, f' (NormalElementaryQuotient.representation W p hp hpk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (f' v) := by
    intro g v
    obtain ⟨x,rfl⟩ := hp g
    have hv : NormalElementaryQuotient.representation W p hp hpk (p x) v = β (q x) v := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [NormalElementaryQuotient.representation_apply,NormalElementaryQuotient.representation_apply]
    rw [hv]
    change c (f (β (q x) v)) = _
    rw [hfj]
    apply c.symm.injective
    rw [c.symm_apply_apply]
    change _ = BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
      (BinaryPermutation.coreRepresentation (Fin 5) (p x) (c (f v)))
    rw [BinaryPermutation.coreEquivNatural_equivariant]
    change _ = BinaryPermutation.naturalRepresentation (Fin 5) (p x) (c.symm (c (f v)))
    rw [c.symm_apply_apply]
    rfl
  refine ⟨p,hp,hpk,f',hf',hfull,?_⟩
  ext v
  rw [NormalElementaryQuotient.mem_fixedSpace_image]
  change c (f v) = 0 ↔ _
  rw [← c.map_zero,c.injective.eq_iff]
  exact sourceMovedQuotientMap_kernel U q hq hker Y A s (pResidual 2 G) hX _ eA v
end CFSG.Quasithin.ChapterB
