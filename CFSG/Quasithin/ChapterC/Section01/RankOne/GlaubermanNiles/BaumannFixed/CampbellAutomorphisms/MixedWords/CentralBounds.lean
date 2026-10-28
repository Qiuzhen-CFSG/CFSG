module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.Escape

/-!
# CentralBounds for Campbell mixed words

The original core-span estimate bounds commutators of every conjugate of F^α. When F^α differs from F, comparison applied to both inverse automorphisms puts the transported fixed layers in the ambient center. These are the two bounds used in Campbell II.6.4(c,d), specialized to the actual Aut(S) family.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

private theorem core_le_sylow (h : InLocalClass S.subtype) : pCore 2 H ≤ S := by
  obtain ⟨T,hT,_⟩ := h.sylow
  have he : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  exact he ▸ pCore_isPGroup.le_sylow_of_normal T

theorem InLocalClass.automorphism_F_inverse_not_le (h : InLocalClass S.subtype)
    (a : MulAut S) (hn : ¬automorphismImage S a (Campbell.F H) ≤ Campbell.F H) :
    ¬automorphismImage S a.symm (Campbell.F H) ≤ Campbell.F H := by
  intro hi
  have hFS := Campbell.F_le_pCore.trans (core_le_sylow S h)
  have hh := automorphismImage_mono S a hi
  have hid : automorphismImage S a (automorphismImage S a.symm (Campbell.F H))=Campbell.F H := by
    simpa only [MulEquiv.symm_symm] using automorphismImage_symm S a.symm (Campbell.F H) hFS
  rw [hid] at hh
  have he : Nat.card (Campbell.F H)=Nat.card (automorphismImage S a (Campbell.F H)) :=
    Nat.card_congr (automorphismImageEquiv S a (Campbell.F H) hFS).toEquiv
  have hEq := Subgroup.eq_of_le_of_card_ge hh he.ge
  exact hn hEq.symm.le

theorem InLocalClass.automorphism_fixed_le_center (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H)
    (hF : ¬automorphismImage S a (Campbell.F H) ≤ Campbell.F H) :
    automorphismImage S a (Campbell.V H ⊓ centralizer (S : Set H)) ≤ center H := by
  have hK := h.sylow_automorphism_fixed_central S hB a hV hF
  intro z hz
  have hzs : z ∈ centralizer (S : Set H) := by
    obtain ⟨y,⟨x,hx,rfl⟩,rfl⟩ := hz
    intro t ht
    let t' : S := ⟨t,ht⟩
    have hc : a.symm t'*x=x*a.symm t' := Subtype.ext (hx.2 _ (a.symm t').property)
    have hc' := congrArg a hc
    have he : t'*a x=a x*t' := by simpa only [map_mul,a.apply_symm_apply] using hc'
    exact congrArg Subtype.val he
  apply mem_center_iff.mpr
  intro g
  have hg : g ∈ Campbell.J (⊤ : Subgroup H) ⊔ pCore 2 H := by
    rw [h.global_thompson_sup_core_eq_top hB]
    trivial
  obtain ⟨k,hk,q,hq,rfl⟩ := mem_sup_of_normal_right.mp hg
  calc
    (k*q)*z = k*(q*z) := mul_assoc _ _ _
    _ = k*(z*q) := by rw [hzs q (core_le_sylow S h hq)]
    _ = (k*z)*q := (mul_assoc _ _ _).symm
    _ = (z*k)*q := by rw [hK hz k hk]
    _ = z*(k*q) := mul_assoc _ _ _

theorem InLocalClass.submaximal_commutator_F_le_fixed (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (X : Subgroup H)
    (hX : ∃ A ∈ elementaryAbelianMaxSubgroups S, X ≤ A) :
    ⁅X,Campbell.F H⁆ ≤ Campbell.V H ⊓ centralizer (S : Set H) := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hSd : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  obtain ⟨n,hn,k,_,_,_,hk,⟨m⟩⟩ := h.natural
  obtain ⟨A,hA,hXA⟩ := hX
  rcases h.campbellF_commutator_dichotomy hB m d hS A (hSd.symm ▸ hA) with hb | he
  · exact (commutator_mono hXA le_rfl).trans (hb.le.trans bot_le)
  · have hs : (d.sylow : Set H)=(S : Set H) := congrArg (fun X : Subgroup H => (X : Set H)) hSd
    rw [hs] at he
    exact (commutator_mono hXA le_rfl).trans he.le

theorem InLocalClass.automorphism_conjugate_core_commutator (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H)
    (g : H) (hg : g ∈ Campbell.J (⊤ : Subgroup H)) :
    ⁅(automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom,
      Campbell.J (pCore 2 H)⁆ ≤
      automorphismImage S a (Campbell.V H ⊓ centralizer (S : Set H)) := by
  have hh := h.original_span_core_frattini (h.precomp_equiv a.symm) hB
    (show ((Campbell.V H).comap (S.subtype.comp a.symm.toMonoidHom)).map S.subtype ≤ pCore 2 H by
      rw [←comap_comap,comap_equiv_eq_map_symm']; exact hV)
  dsimp only at hh
  have hr : (S.subtype.comp a.symm.toMonoidHom).range=S := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr a.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  rw [hr,←comap_comap,comap_equiv_eq_map_symm',←comap_comap,comap_equiv_eq_map_symm'] at hh
  apply (commutator_mono ?_ le_rfl).trans hh.2.1
  rintro x ⟨y,hy,rfl⟩
  exact subset_closure ⟨g,hg,y,hy,rfl⟩
end CFSG.Quasithin.ChapterC.GlaubermanNiles
