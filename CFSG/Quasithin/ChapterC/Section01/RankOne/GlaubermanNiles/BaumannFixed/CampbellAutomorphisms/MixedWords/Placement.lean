module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.AutomorphismOrbit
public import Theory.GroupTheory.SubgroupAutomorphismImages.Operations

/-!
# Placement of Campbell's first mixed words

A submaximal elementary subgroup inside the two-core extends to a maximum
one inside that core. This makes conjugation and subsequent Sylow
automorphism transport legitimate. Theorem 6 shows that the inverse
image of an involutory conjugate of F^α centralizes F, placing that
actual mixed word back in the two-core. This is Campbell II.6.4(a,b),
printed pp.31–32, for the original Sylow automorphisms used by C.1.18.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

private theorem sylow_core_le (h : InLocalClass S.subtype) : pCore 2 H ≤ S := by
  obtain ⟨T,hT,_⟩ := h.sylow
  have he : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  exact he ▸ pCore_isPGroup.le_sylow_of_normal T

theorem InLocalClass.submaximal_core_extension (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (X : Subgroup H)
    (hX : ∃ A ∈ elementaryAbelianMaxSubgroups S, X ≤ A)
    (hXQ : X ≤ pCore 2 H) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, A ≤ pCore 2 H ∧ X ≤ A := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hS' : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  obtain ⟨A,hA,hXA⟩ := hX
  refine ⟨(A ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H),?_,?_,?_⟩
  · simpa only [hS'] using h.omegaCore_replacement_maximal hB d A (hS'.symm ▸ hA)
  · exact sup_le inf_le_right (fun x hx => ((mem_omegaOneCenterAmbient_iff _ x).mp hx).1)
  · exact (le_inf hXA hXQ).trans le_sup_left

theorem InLocalClass.submaximal_core_conjugate (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (X : Subgroup H)
    (hX : ∃ A ∈ elementaryAbelianMaxSubgroups S, X ≤ A)
    (hXQ : X ≤ pCore 2 H) (g : H) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, A ≤ pCore 2 H ∧
      X.map (MulAut.conj g).toMonoidHom ≤ A := by
  obtain ⟨A,hA,hAQ,hXA⟩ := h.submaximal_core_extension S hB X hX hXQ
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  refine ⟨A.map (MulAut.conj g).toMonoidHom,?_,?_,map_mono hXA⟩
  · simpa only [←hST] using maxElementary_conjugate_of_le_core T g A (hST ▸ hA) hAQ
  · rintro x ⟨y,hy,rfl⟩
    exact (inferInstance : (pCore 2 H).Normal).conj_mem y (hAQ hy) g

theorem InLocalClass.automorphism_F_submaximal (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, automorphismImage S a (Campbell.F H) ≤ A := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hS' : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  obtain ⟨A,hA,hFA⟩ := h.campbellF_le_some_maxElementary hB d
  exact ⟨automorphismImage S a A,automorphismImage_maxElementary S a A (hS' ▸ hA),
    automorphismImage_mono S a hFA⟩

theorem InLocalClass.automorphism_F_conjugate_submaximal (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H) (g : H) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, A ≤ pCore 2 H ∧
      (automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom ≤ A := by
  have hs := h.sylow_automorphism_span S hB a hV
  exact h.submaximal_core_conjugate S hB _ (h.automorphism_F_submaximal S hB a)
    ((le_conjugateSpanBy _ _).trans hs.1) g

theorem InLocalClass.inverse_conjugate_core (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H)
    (g : H) (hg : g ∈ Campbell.J (⊤ : Subgroup H))
    (hg2 : ∃ n, orderOf g=2^n) :
    automorphismImage S a.symm
      ((automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom) ≤ pCore 2 H := by
  have hc := h.two_element_conjugates_commute S hB a hV g 1 hg hg2 (one_mem _)
  dsimp only at hc
  have hc' : automorphismImage S a (Campbell.F H) ≤ centralizer
      ((automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom : Set H) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    have h1 : (MulAut.conj (1 : H)).toMonoidHom = MonoidHom.id H := by
      ext x
      simp
    have hg1 : (MulAut.conj (g * 1)).toMonoidHom = (MulAut.conj g).toMonoidHom := by
      ext x
      simp
    rw [h1, hg1] at hc
    simpa using hc
  have ha := automorphismImage_le_centralizer S a.symm _ _ (le_centralizer_iff.mp hc')
  rw [automorphismImage_symm S a (Campbell.F H) (Campbell.F_le_pCore.trans (sylow_core_le S h))] at ha
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨n,hn,k,_,_,_,hk,⟨m⟩⟩ := h.natural
  apply (h.sylow_centralizer_campbellF_le_core hB m d).trans'
  apply le_inf _ ha
  simpa only [hS,range_subtype] using automorphismImage_le S a.symm
    ((automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom)

theorem InLocalClass.inverse_conjugate_submaximal (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H)
    (g : H) (hg : g ∈ Campbell.J (⊤ : Subgroup H))
    (hg2 : ∃ n, orderOf g=2^n) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, A ≤ pCore 2 H ∧
      automorphismImage S a.symm
        ((automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom) ≤ A := by
  obtain ⟨A,hA,hAQ,hYA⟩ := h.automorphism_F_conjugate_submaximal S hB a hV g
  exact h.submaximal_core_extension S hB _
    ⟨automorphismImage S a.symm A,automorphismImage_maxElementary S a.symm A hA,
      automorphismImage_mono S a.symm hYA⟩ (h.inverse_conjugate_core S hB a hV g hg hg2)
end CFSG.Quasithin.ChapterC.GlaubermanNiles
