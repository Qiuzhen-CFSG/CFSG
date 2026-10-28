module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.MixedWords.Placement

/-!
# The genuine escaping-image alternative

If the actual Sylow automorphism image V^α escapes O₂(H), the inverse
image F^(α⁻¹) also escapes. Its noncore point detects the entire fixed
subgroup of V. Submaximal control therefore identifies V^α∩O₂(H) with
the transported fixed subgroup. The natural relative-index bound then
proves V^α O₂(H)=S. This is Campbell II.7.1's exceptional branch,
printed p.33, retaining the original automorphism and ambient maps.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

theorem InLocalClass.escaping_automorphism_core_intersection
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hX : ¬ automorphismImage S a (Campbell.V H) ≤ pCore 2 H) :
    automorphismImage S a (Campbell.V H) ⊓ pCore 2 H =
      automorphismImage S a (Campbell.V H ⊓ centralizer (S : Set H)) := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hSd : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  have hQS : pCore 2 H ≤ S := hSd ▸ pCore_isPGroup.le_sylow_of_normal d.sylow
  have hVS : Campbell.V H ≤ S := Campbell.V_le_pCore.trans hQS
  have hFS : Campbell.F H ≤ S := Campbell.F_le_pCore.trans hQS
  obtain ⟨n,hn,k,_,_,_,hk,⟨m⟩⟩ := h.natural
  let X := automorphismImage S a (Campbell.V H)
  let Z := Campbell.V H ⊓ centralizer (S : Set H)
  have hCF : S ⊓ centralizer (Campbell.F H : Set H) ≤ pCore 2 H := by
    simpa only [hSd] using h.sylow_centralizer_campbellF_le_core hB m d
  have hVC : Campbell.V H ≤ centralizer (pCore 2 H : Set H) :=
    Campbell.V_le_omegaCore.trans (fun x hx => ((mem_omegaOneCenterAmbient_iff _ x).mp hx).2.2)
  have hinverse : ¬ automorphismImage S a.symm (Campbell.F H) ≤ pCore 2 H := by
    intro hn
    have hc := hVC.trans (centralizer_le hn)
    have hc' := automorphismImage_le_centralizer S a _ _ hc
    have hid : automorphismImage S a (automorphismImage S a.symm (Campbell.F H))=Campbell.F H := by
      simpa only [MulEquiv.symm_symm] using automorphismImage_symm S a.symm (Campbell.F H) hFS
    rw [hid] at hc'
    exact hX ((le_inf (automorphismImage_le S a (Campbell.V H)) hc').trans hCF)
  obtain ⟨t,ht,htQ⟩ := Set.not_subset.mp hinverse
  have htS : t ∈ S := automorphismImage_le S a.symm _ ht
  have hfix := h.campbell_fixed_by_noncore_actor hB t
    (by simpa only [range_subtype] using htS) htQ
  rw [range_subtype] at hfix
  obtain ⟨A,hA,hFA⟩ := h.automorphism_F_submaximal S hB a
  have hXA : X ≤ A := (automorphismImage_mono S a Campbell.V_le_F).trans hFA
  have hXC : X ⊓ pCore 2 H ≤ centralizer (Campbell.F H : Set H) :=
    (h.campbellF_submaximal_control hB m d X A (hSd.symm ▸ hA) hXA).1
  apply le_antisymm
  · intro x hx
    obtain ⟨y,⟨v,hv,rfl⟩,rfl⟩ := hx.1
    have hvZ : (v:H) ∈ Z := by
      change (v:H) ∈ Campbell.V H ⊓ centralizer (S : Set H)
      rw [←hfix]
      refine ⟨hv,mem_centralizer_singleton_iff.mpr ?_⟩
      obtain ⟨y,⟨f,hf,rfl⟩,rfl⟩ := ht
      have hc : (f:H)*(a v:H)=(a v:H)*(f:H) := hXC hx f hf
      have he : f*a v=a v*f := Subtype.ext hc
      have he' := congrArg a.symm he
      have hout : a.symm f*v=v*a.symm f := by
        simpa only [map_mul,a.symm_apply_apply] using he'
      exact (congrArg Subtype.val hout).symm
    exact mem_map_of_mem S.subtype (mem_map_of_mem a.toMonoidHom hvZ)
  · refine le_inf (automorphismImage_mono S a inf_le_left) ?_
    apply (le_inf (automorphismImage_le S a Z) ?_).trans hCF
    rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩ f hf
    let f' : S := ⟨f,hFS hf⟩
    have he : a.symm f'*z=z*a.symm f' := Subtype.ext (hz.2 _ (a.symm f').property)
    have hh := congrArg a he
    have hout : f'*a z=a z*f' := by
      simpa only [map_mul,a.apply_symm_apply] using hh
    exact congrArg Subtype.val hout

theorem InLocalClass.escaping_automorphism_sup_core
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hX : ¬ automorphismImage S a (Campbell.V H) ≤ pCore 2 H) :
    automorphismImage S a (Campbell.V H) ⊔ pCore 2 H=S := by
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
  have hVS : Campbell.V H ≤ S := Campbell.V_le_pCore.trans hQS
  let V := Campbell.V H
  let Z := V ⊓ centralizer (S : Set H)
  let X := automorphismImage S a V
  have hXQ := h.escaping_automorphism_core_intersection S hB a hX
  have ha := relIndex_map_map_of_injective (f := a.toMonoidHom) (Z.subgroupOf S) (V.subgroupOf S) a.injective
  have hb := relIndex_map_map_of_injective ((Z.subgroupOf S).map a.toMonoidHom)
    ((V.subgroupOf S).map a.toMonoidHom) S.subtype_injective
  have hc := relIndex_map_map_of_injective (Z.subgroupOf S) (V.subgroupOf S) S.subtype_injective
  rw [map_subgroupOf_eq_of_le (inf_le_left.trans hVS),map_subgroupOf_eq_of_le hVS] at hc
  have hi : (automorphismImage S a Z).relIndex X = Z.relIndex V := hb.trans (ha.trans hc.symm)
  have hXindex : (pCore 2 H).relIndex X = Z.relIndex V := by
    rw [←inf_relIndex_left X (pCore 2 H),hXQ]
    exact hi
  have hl := h.campbell_natural_index_ge_sylow_index hB
  rw [range_subtype,←inf_relIndex_left V (centralizer (S : Set H)),←hXindex] at hl
  have hsupS : pCore 2 H ⊔ X ≤ S := sup_le hQS (automorphismImage_le S a V)
  have hmult := relIndex_mul_relIndex (pCore 2 H) (pCore 2 H ⊔ X) S le_sup_left hsupS
  rw [relIndex_sup_left] at hmult
  let : (pCore 2 H).IsFiniteRelIndex X := isFiniteRelIndex_of_finiteIndex
  let : (pCore 2 H ⊔ X).IsFiniteRelIndex S := isFiniteRelIndex_of_finiteIndex
  have hpos : 0<(pCore 2 H).relIndex X := Nat.pos_of_ne_zero relIndex_ne_zero
  have hone : (pCore 2 H ⊔ X).relIndex S=1 := by
    have hle : (pCore 2 H ⊔ X).relIndex S ≤ 1 := by nlinarith
    exact le_antisymm hle (Nat.one_le_iff_ne_zero.mpr relIndex_ne_zero)
  rw [sup_comm]
  exact le_antisymm hsupS (relIndex_eq_one.mp hone)
end CFSG.Quasithin.ChapterC.GlaubermanNiles
