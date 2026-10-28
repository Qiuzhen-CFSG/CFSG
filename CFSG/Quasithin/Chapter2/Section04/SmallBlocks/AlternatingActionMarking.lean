module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingNormalizerSource
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup.Thompson
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# The actual symmetric-five quotient and transposition images

For the selected single A₅ block, the normalizer of its binary natural
module gives a permutation action of H. The block centralizer theorem
identifies its kernel with O₂(H). The moved Thompson subgroup supplies an
odd permutation, making the action surjective onto S₅.

A maximum elementary subgroup whose image has order two is an offender
on the actual natural module. The five-point offender classification
therefore identifies that image with a transposition subgroup. The final
source application retains the original subtype maps and relative index;
it supplies the marked input to the mixed-normalizer exclusion in 2.4.27.

Source: Aschbacher–Smith, 2.4.27–29, printed pp.544–545, using C.5.4(3)
and B.3.2 (refs/quasithin.pdf).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher BinaryPermutation
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource ChapterC.Section05.BlockAnalysis
open ChapterC.Section05.BlockAnalysis.AlternatingSetup
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_marked_action
    (d : MinimalBlockSetup M) (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    ∃ (q : d.H →* Equiv.Perm (Fin 5))
      (e : (blockU d.block).map d.block.subtype ≃*
        Multiplicative (core (Fin 5))),
      Function.Surjective q ∧ q.ker = pCore 2 d.H ∧
      q.ker = centralizer ((blockU d.block).map d.block.subtype : Set d.H) ∧
      ∀ (s : d.H) (u : (blockU d.block).map d.block.subtype),
        (e.symm (Multiplicative.ofAdd
          (coreRepresentation (Fin 5) (q s) (e u).toAdd)) : d.H) =
            s * (u : d.H) * s⁻¹ := by
  let K := d.block.map d.H.subtype
  let U := (blockU d.block).map d.block.subtype
  have hKn : d.block.Normal := hsingle ▸ d.L0_normal
  let := hKn
  have hK : IsAlternatingBlock d.block 5 := hA.of_mulEquiv
    (d.block.equivMapOfInjective d.H.subtype d.H.subtype_injective).symm
  have hHK : d.H ≤ normalizer (K : Set G) := by
    change d.H ≤ normalizer (d.block.map d.H.subtype : Set G)
    simpa only [normalizer_eq_top, ←MonoidHom.range_eq_map,range_subtype] using
      d.block.le_normalizer_map d.H.subtype
  have hU : U.map d.H.subtype = sourceModule K := by
    exact (moduleLayer_map d.H.subtype d.H.subtype_injective d.block).symm
  obtain ⟨q,e,hker,himage,he⟩ := exists_action hA (map_subtype_le _) hHK
  let e' : U ≃* Multiplicative (core (Fin 5)) :=
    (U.equivMapOfInjective d.H.subtype d.H.subtype_injective).trans
      ((MulEquiv.subgroupCongr hU).trans e)
  have hk : q.ker = centralizer (U : Set d.H) := by
    rw [hker,←hU]
    ext g
    constructor
    · intro hg u hu
      exact Subtype.ext (hg u (mem_map_of_mem d.H.subtype hu))
    · rintro hg u ⟨v,hv,rfl⟩
      exact congrArg Subtype.val (hg v hv)
  have he' (s : d.H) (u : U) :
      (e'.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (q s) (e' u).toAdd)) : d.H) =
          s * (u : d.H) * s⁻¹ := by
    apply Subtype.ext
    have hev (w : Multiplicative (core (Fin 5))) :
        ((e'.symm w : U) : G) = (e.symm w : G) := by
      have hh : (⟨((e'.symm w : U) : G),by rw [←hU]; exact mem_map_of_mem _ (e'.symm w).property⟩ : sourceModule K) = e.symm w := by
        apply e.injective
        change e' (e'.symm w) = e (e.symm w)
        rw [e'.apply_symm_apply,e.apply_symm_apply]
      exact congrArg Subtype.val hh
    exact (hev _).trans (he s ⟨u,by rw [←hU]; exact mem_map_of_mem _ u.property⟩)
  have hprod (g : d.H) : ∃ k ∈ d.block, ∃ s ∈ (d.S : Subgroup d.H), k*s=g := by
    obtain ⟨k,s,hg⟩ := d.factorization g
    exact ⟨k,hsingle ▸ k.property,s,s.property,hg.symm⟩
  have hcore : centralizer (U : Set d.H) = pCore 2 d.H :=
    lemma_C_1_11_single d.block d.block_type.1 d.S hprod
  let : U.Normal := inferInstanceAs (((blockU d.block).map d.block.subtype).Normal)
  let : IsElementaryAbelian 2 U := by
    let := hK.2.1.elementary
    exact IsElementaryAbelian.map d.block.subtype
  have hUS : U ≤ d.S := (le_centralizer U).trans
    (hcore.le.trans (pCore_isPGroup.le_sylow_of_normal d.S))
  have hJ : ¬ elementaryAbelianMaxJ (d.S : Subgroup d.H) ≤ centralizer (U : Set d.H) := by
    intro hh
    have hm := map_mono (f := d.H.subtype) hh
    rw [←elementaryAbelianMaxJ_map_injective d.H.subtype d.H.subtype_injective] at hm
    exact thompson_moves_of_commutator K _ hA.2.1 d.moved
      (hm.trans (by
        rw [←hU]
        exact map_centralizer_le_centralizer_image _ _))
  have hsurj := surjective_of_thompson_moves U q hk e' he' d.S hUS hJ
    (himage ▸ map_le_range q _)
  exact ⟨q,e',hsurj,hk.trans hcore,hk,he'⟩
end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
open ChapterB.Offenders
variable {D : Type*} [Group D] [Finite D]

theorem transposition_image_of_maximal_elementary
    (V : Subgroup D) [V.Normal] [IsElementaryAbelian 2 V]
    (q : D →* Equiv.Perm (Fin 5)) (hk : q.ker = centralizer (V : Set D))
    (e : V ≃* Multiplicative (core (Fin 5)))
    (he : ∀ (s : D) (u : V),
      (e.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (q s) (e u).toAdd)) : D) = s * (u : D) * s⁻¹)
    (R A : Subgroup D) (hVR : V ≤ R)
    (hA : A ∈ elementaryAbelianMaxSubgroups R) (hi : q.ker.relIndex A = 2) :
    ∃ t : Equiv.Perm (Fin 5), t.IsSwap ∧ A.map q = zpowers t := by
  have hc : Nat.card (A.map q) = 2 := (relIndex_ker A q).symm.trans hi
  have hne : A.map q ≠ ⊥ := by intro h; simp [h] at hc
  obtain ⟨m,hm,_,g,hg⟩ := max_image_caseA V q hk e he R A hVR hA hne
  let t := (MulAut.conj g) (pairSwap 5 0)
  have ht : t.IsSwap :=
    ⟨g 0,g 1,g.injective.ne (by decide),Equiv.symm_trans_swap_trans (0 : Fin 5) 1 g⟩
  have htA : t ∈ A.map q := by
    rw [hg]
    exact mem_map_of_mem _ (pairSwap_mem (n := 5) (m := m) 0 hm)
  refine ⟨t,ht,?_⟩
  symm
  apply eq_of_le_of_card_ge (zpowers_le.mpr htA)
  rw [Nat.card_zpowers,ht.orderOf,hc]
end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup

namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.BlockAnalysis.AlternatingSetup
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem MinimalBlockSetup.single_alternating_transposition_action
    (d : MinimalBlockSetup M) (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (A : Subgroup G)
    (hmax : A ∈ elementaryAbelianMaxSubgroups ((d.S : Subgroup d.H).map d.H.subtype))
    (hi : (twoCore d.H).relIndex A = 2) :
    ∃ q : d.H →* Equiv.Perm (Fin 5), Function.Surjective q ∧
      q.ker = pCore 2 d.H ∧
      ∃ t : Equiv.Perm (Fin 5), t.IsSwap ∧ (A.subgroupOf d.H).map q = zpowers t := by
  obtain ⟨q,e,hq,hker,hC,he⟩ := d.single_alternating_marked_action hsingle hA
  let U := (blockU d.block).map d.block.subtype
  have hAi : IsAlternatingBlock d.block 5 := hA.of_mulEquiv
    (d.block.equivMapOfInjective d.H.subtype d.H.subtype_injective).symm
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let : U.Normal := inferInstanceAs (((blockU d.block).map d.block.subtype).Normal)
  let : IsElementaryAbelian 2 U := by
    let := hAi.2.1.elementary
    exact IsElementaryAbelian.map d.block.subtype
  have hUS : U ≤ d.S := (le_centralizer U).trans
    ((hC.symm.trans hker).le.trans (pCore_isPGroup.le_sylow_of_normal d.S))
  have hAH : A ≤ d.H := hmax.1.trans (map_subtype_le _)
  have hm : A.subgroupOf d.H ∈ elementaryAbelianMaxSubgroups (d.S : Subgroup d.H) := by
    apply (maxFamily_map_injective_iff d.H.subtype d.H.subtype_injective _ _).mp
    rwa [map_subgroupOf_eq_of_le hAH]
  have hi' : q.ker.relIndex (A.subgroupOf d.H) = 2 := by
    rw [hker]
    have hc : (twoCore d.H).subgroupOf d.H = pCore 2 d.H := by
      ext x
      constructor
      · rintro ⟨v,hv,hvx⟩
        exact (d.H.subtype_injective hvx) ▸ hv
      · intro hx
        exact mem_map_of_mem d.H.subtype hx
    rw [←hc,relIndex_subgroupOf hAH]
    exact hi
  obtain ⟨t,ht,heq⟩ := transposition_image_of_maximal_elementary U q hC e he
    d.S (A.subgroupOf d.H) hUS hm hi'
  exact ⟨q,hq,hker,t,ht,heq⟩
end CFSG.Quasithin.Chapter2
