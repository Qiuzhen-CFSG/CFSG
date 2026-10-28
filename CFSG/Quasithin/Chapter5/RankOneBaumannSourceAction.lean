module
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceCore
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Baumann

/-!
# Marking the original A5 action and its conjugate

The fixed kernel in the earlier five-point section vanishes because its support
is the original alternating block. Relabelling that actual section puts the
Baumann image at the two disjoint transpositions. Conjugating LT transports both
the section and its module, while retaining the original Baumann subgroup.
The local domains suffice for the crossing argument; no later recognition or
chosen-module invariance is used.

Source: Aschbacher--Smith 5.1.7(1), p.633, using 5.1.2 and E.2.3.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterB ChapterC
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
attribute [local instance] ChapterB.RankOneBaumann.semilinear_moved_elementary

theorem Input.moved_sylow_normalizes (h : Input KnownSimple.IsKnownSimple T L W n) :
    (T : Subgroup G) ≤ normalizer ((⁅W,L⁆ : Subgroup G) : Set G) :=
  le_sup_right.trans (reduced_normalizes h.commutator_reduced)

theorem Input.normalizer_of_local_normal (h : Input KnownSimple.IsKnownSimple T L W n)
    (D : Subgroup G) (hne : D ≠ ⊥) (hDT : D ≤ (T : Subgroup G))
    (hn : (D.subgroupOf (L ⊔ (T : Subgroup G))).Normal) :
    normalizer (D : Set G) ≤ normalizer (L : Set G) :=
  normalizer_le_of_unique_maximalTwoLocal
    (Chapter5.RankOneBaumannSource.unique_sylow_join h.qtke h.maximal_local h.sylow_normalizes)
    (T.isPGroup'.to_le hDT) hne
    ((normal_subgroupOf_iff_le_normalizer (hDT.trans le_sup_right)).mp hn)

theorem Input.moved_thompson_moves_of_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    ¬elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer ((⁅W,L⁆ : Subgroup G) : Set G) := by
  intro hj
  let := h.quotient_quasisimple
  exact hout (Chapter5.RankOneBaumannSource.baumann_normalizer_of_thompson_centralizes
    h.qtke h.maximal_local h.sylow_normalizes h.commutator_reduced.1
    h.commutator_input.reduced_internal h.quotient_center_eq_bot h.commutator_input.noncentral hj)

theorem Input.moved_disjoint_centralizer_of_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    Disjoint ⁅W,L⁆ (centralizer (L : Set G)) := by
  obtain ⟨_,hb,hV,_⟩ := h.alternating_block_of_baumann_escape hout
  have hz : blockU L ⊓ center L = ⊥ := by
    rw [←blockFixed_map,hb.blockFixed_eq_bot,Subgroup.map_bot]
  rw [disjoint_def]
  intro x hx hc
  rw [←hV] at hx
  obtain ⟨v,hv,rfl⟩ := hx
  have hvZ : v ∈ center L := by
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext (hc l l.property)
  exact congrArg Subtype.val (show v=1 from hz.le ⟨hv,hvZ⟩)

theorem Input.baumann_core_disjoint_of_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    Disjoint ⁅W,L⁆ (baumann (T : Subgroup G) ⊓ centralizer (L : Set G)) :=
  (h.moved_disjoint_centralizer_of_escape hout).mono_right inf_le_right

theorem Input.baumann_core_centralizer_of_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    (L ⊔ baumann (T : Subgroup G)).pCoreIn 2 =
      baumann (T : Subgroup G) ⊓ centralizer ((⁅W,L⁆ : Subgroup G) : Set G) := by
  obtain ⟨_,hb,hV,_⟩ := h.alternating_block_of_baumann_escape hout
  have he := Section05.CounterexampleCharacteristic.ReducedMarking.normal_short_extension_centralizer
    L (baumann (T : Subgroup G)) hb.2.1
    (T.isPGroup'.to_le (show baumann (T : Subgroup G) ≤ (T : Subgroup G) from inf_le_left))
    (inf_le_left.trans h.sylow_normalizes)
  change (L ⊔ baumann (T : Subgroup G)) ⊓ centralizer ((blockU L).map L.subtype : Set G) = _ at he
  rw [hV] at he
  exact le_antisymm
    (le_inf (h.baumann_core_le_of_escape hout) (he.ge.trans inf_le_right))
    ((inf_le_inf le_sup_right le_rfl).trans he.le)

/-- The original five-point section is an isomorphism: its fixed kernel vanishes
on the original moved module, by the actual alternating block. -/
theorem Input.exists_baumann_action_marking
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    ∃ q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 5),
      ∃ m : Multiplicative (BinaryPermutation.core (Fin 5)) →* G,
        Function.Surjective q ∧ Function.Injective m ∧ m.range = ⁅W,L⁆ ∧
        (∀ (g : (L ⊔ (T : Subgroup G) : Subgroup G)) (x : BinaryPermutation.core (Fin 5)),
          (g:G) * m (Multiplicative.ofAdd x) * (g:G)⁻¹ =
            m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (q g) x))) ∧
        ((baumann (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map q = Offenders.D 5 := by
  let H := L ⊔ (T : Subgroup G)
  let U := W.subgroupOf H
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let V := ⁅U,pResidual 2 H⁆
  let R := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hVmap : V.map H.subtype = ⁅W,L⁆ := h.local_moved_map
  obtain ⟨q,hq,hk,f,hf,he,hfk⟩ := h.five_section_of_baumann_escape hout
  change q.ker = centralizer (V : Set H) at hk
  let ρ := NormalElementaryQuotient.representation V q hq hk
  have hfi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro v hv
    have hvf : v ∈ fixedSpace ρ ((pResidual 2 H).map q) := hfk ▸ hv
    have hc := (NormalElementaryQuotient.mem_fixedSpace_image V q hq hk (pResidual 2 H) v).mp hvf
    have hcg : ((v.toMul : H) : G) ∈ centralizer (L : Set G) := by
      intro l hl
      obtain ⟨r,hr,hval⟩ := h.local_residual_eq.ge hl
      have hh := congrArg H.subtype (hc r hr)
      change (r:G) = l at hval
      change (r:G) * ((v.toMul : H) : G) = ((v.toMul : H) : G) * (r:G) at hh
      simpa only [hval] using hh
    have hvG : ((v.toMul : H) : G) = 1 :=
      disjoint_def.mp (h.moved_disjoint_centralizer_of_escape hout)
        (hVmap ▸ mem_map_of_mem H.subtype v.toMul.property) hcg
    exact Additive.toMul.injective (Subtype.ext (Subtype.ext hvG))
  let e := LinearEquiv.ofBijective f ⟨hfi,hf⟩
  let m : Multiplicative (BinaryPermutation.core (Fin 5)) →* G := {
    toFun x := ((e.symm x.toAdd).toMul : H)
    map_one' := by change (((e.symm 0).toMul : H) : G) = 1; rw [map_zero]; rfl
    map_mul' x y := by
      change (((e.symm (x.toAdd+y.toAdd)).toMul : H) : G) = _
      rw [map_add]; rfl }
  have hm : Function.Injective m := by
    intro x y hh
    apply Multiplicative.toAdd.injective
    apply e.symm.injective
    exact Additive.toMul.injective (Subtype.ext (Subtype.ext hh))
  have hr : m.range = ⁅W,L⁆ := by
    rw [←hVmap]
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨_,(e.symm y.toAdd).toMul.property,rfl⟩
    · rintro ⟨v,hv,rfl⟩
      refine ⟨Multiplicative.ofAdd (e (Additive.ofMul ⟨v,hv⟩)),?_⟩
      change (((e.symm (e (Additive.ofMul ⟨v,hv⟩))).toMul : H) : G) = _
      rw [e.symm_apply_apply]
      rfl
  have hme : ∀ (g:H) (x : BinaryPermutation.core (Fin 5)),
      (g:G) * m (Multiplicative.ofAdd x) * (g:G)⁻¹ =
        m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (q g) x)) := by
    intro g x
    have heq : ρ (q g) (e.symm x) = e.symm (BinaryPermutation.coreRepresentation (Fin 5) (q g) x) := by
      apply e.injective
      rw [e.apply_symm_apply]
      change f (ρ (q g) (e.symm x)) = _
      rw [he]
      exact congrArg (BinaryPermutation.coreRepresentation (Fin 5) (q g)) (e.apply_symm_apply x)
    have hh := congrArg (fun v : Additive V => ((v.toMul : H) : G)) heq
    rw [NormalElementaryQuotient.representation_apply] at hh
    exact hh
  have hRmap : (R : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hVR : V ≤ (R : Subgroup H) := by
    have hr := h.reduced_internal.moved U
    exact hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal R)
  have hJR : ¬elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (V : Set H) := by
    intro hc
    apply h.moved_thompson_moves_of_escape hout
    have hjm : (elementaryAbelianMaxJ (R : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hRmap]
    rw [←hjm,←hVmap]
    rintro _ ⟨x,hx,rfl⟩ _ ⟨v,hv,rfl⟩
    exact congrArg H.subtype (hc hx v hv)
  obtain ⟨a,ha⟩ := (SymmetricFive.source_thompson_baumann V R hVR q hq hk f hf he
    (fun v hv _ _ => by
      have hz : v = 0 := hfi (hv.trans (map_zero f).symm)
      subst v
      exact map_zero _) hJR).2.2
  have hB : baumann (R : Subgroup H) = (baumann (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    change ((R : Subgroup H) ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ (R : Subgroup H)) : Set H)).map H.subtype = _
    rw [baumann_map_injective H.subtype H.subtype_injective]
    rw [map_subgroupOf_eq_of_le (show baumann (T : Subgroup G) ≤ H from inf_le_left.trans le_sup_right),hRmap]
    rfl
  rw [hB] at ha
  let c : Multiplicative (BinaryPermutation.core (Fin 5)) ≃* Multiplicative (BinaryPermutation.core (Fin 5)) := {
    toFun x := Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) a x.toAdd)
    invFun x := Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) a⁻¹ x.toAdd)
    left_inv x := by
      change Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) a⁻¹
        (BinaryPermutation.coreRepresentation (Fin 5) a x.toAdd)) = x
      rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one]; rfl
    right_inv x := by
      change Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) a
        (BinaryPermutation.coreRepresentation (Fin 5) a⁻¹ x.toAdd)) = x
      rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one]; rfl
    map_mul' x y := congrArg Multiplicative.ofAdd (map_add _ _ _) }
  refine ⟨(MulAut.conj a⁻¹).toMonoidHom.comp q,m.comp c.toMonoidHom,
    (MulAut.conj a⁻¹).surjective.comp hq,hm.comp c.injective,?_,?_,?_⟩
  · rw [MonoidHom.range_comp,c.toMonoidHom.range_eq_top.mpr c.surjective,←MonoidHom.range_eq_map,hr]
  · intro g x
    change (g:G) * m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) a x)) * (g:G)⁻¹ = _
    rw [hme]
    apply congrArg (fun v => m (Multiplicative.ofAdd v))
    change BinaryPermutation.coreRepresentation (Fin 5) (q g) (BinaryPermutation.coreRepresentation (Fin 5) a x) =
      BinaryPermutation.coreRepresentation (Fin 5) a (BinaryPermutation.coreRepresentation (Fin 5) (a⁻¹ * q g * a) x)
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,mul_inv_cancel_left]
  · rw [←map_map,ha,map_map]
    have hc : (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom = MonoidHom.id (Equiv.Perm (Fin 5)) := by
      ext p
      simp [MulAut.conj_apply,mul_assoc]
    rw [hc,map_id]

/-- Transport the same local action to the actual conjugate of LT. Its domain
contains S; no action of the full module normalizer is assumed. -/
theorem Input.exists_conjugate_baumann_action_marking
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (g : G) (hg : g ∈ normalizer (baumann (T : Subgroup G) : Set G)) :
    let U := (⁅W,L⁆ : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom
    ∃ N : Subgroup G, baumann (T : Subgroup G) ≤ N ∧
      ∃ q : N →* Equiv.Perm (Fin 5),
      ∃ m : Multiplicative (BinaryPermutation.core (Fin 5)) →* G,
        Function.Surjective q ∧ Function.Injective m ∧ m.range = U ∧
        (∀ (n : N) (x : BinaryPermutation.core (Fin 5)),
          (n:G) * m (Multiplicative.ofAdd x) * (n:G)⁻¹ =
            m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (q n) x))) ∧
        ((baumann (T : Subgroup G)).subgroupOf N).map q = Offenders.D 5 := by
  obtain ⟨q,m,hq,hm,hr,he,hS⟩ := h.exists_baumann_action_marking hout
  let e := MulAut.conj g⁻¹
  let H := L ⊔ (T : Subgroup G)
  let N := H.map e.toMonoidHom
  let f : N ≃* H := {
    toFun := fun n => ⟨e.symm n,mem_map_equiv.mp n.property⟩
    invFun := fun n => ⟨e n,mem_map_of_mem e.toMonoidHom n.property⟩
    left_inv := fun n => Subtype.ext (e.apply_symm_apply n)
    right_inv := fun n => Subtype.ext (e.symm_apply_apply n)
    map_mul' := fun n k => Subtype.ext (map_mul e.symm (n:G) (k:G)) }
  let S := baumann (T : Subgroup G)
  have hSe : S.map e.toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (S : Set G)).inv_mem hg)
  have hSH : S ≤ H := inf_le_left.trans le_sup_right
  refine ⟨N,hSe.ge.trans (map_mono hSH),q.comp f.toMonoidHom,e.toMonoidHom.comp m,
    hq.comp f.surjective,e.injective.comp hm,?_,?_,?_⟩
  · rw [MonoidHom.range_comp,hr]
  · intro n x
    have hh := congrArg e (he (f n) x)
    have hf : e (f n : G) = (n:G) := e.apply_symm_apply (n:G)
    simpa only [map_mul,map_inv,hf,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom] using hh
  · rw [←hS]
    ext p
    constructor
    · rintro ⟨n,hn,rfl⟩
      refine ⟨f n,?_,rfl⟩
      change e.symm n ∈ S
      exact mem_map_equiv.mp (hSe.symm ▸ hn)
    · rintro ⟨n,hn,rfl⟩
      refine ⟨f.symm n,?_,by simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,f.apply_symm_apply]⟩
      change e n ∈ S
      exact hSe ▸ mem_map_of_mem e.toMonoidHom hn

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
