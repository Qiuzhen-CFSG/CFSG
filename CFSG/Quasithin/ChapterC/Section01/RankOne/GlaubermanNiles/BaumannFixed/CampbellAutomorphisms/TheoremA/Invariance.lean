module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.ReplacementAction
public import Theory.GroupTheory.ElementaryReplacementInvariance
/-!
# Campbell II.7.6 in the original local group

The mixed conjugates commute for every noncore elementary actor. The
maximum replacement argument therefore makes its commutator invariant
under those actors; they generate A, so the entire A normalizes it.
The maximum-family premise is supplied by MixedReplacementTransport.
Source: Campbell II.7.6, printed pp.35–36.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open CampbellTheoremA
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

theorem InLocalClass.mixed_commutator_normalized_of_maximum
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (hF : ¬imageF S a ≤ Campbell.F H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S) (hAQ : ¬A ≤ pCore 2 H)
    (M : Subgroup H) (hM : S ≤ M ∧ M ⋖ ⊤) (g : H)
    (hgK : g ∈ Campbell.J (⊤ : Subgroup H)) (hg2 : g^2=1) (hgM : g ∉ M)
    (hW : mixedActor S a g ⊔ (replacement S a A g ⊓ centralizer (mixedActor S a g : Set H)) ∈
      elementaryAbelianMaxSubgroups S) :
    A ≤ normalizer ((⁅replacement S a A g,mixedActor S a g⁆ : Subgroup H) : Set H) := by
  let B := replacement S a A g
  let Y := mixedActor S a g
  let N := normalizer ((⁅B,Y⁆ : Subgroup H) : Set H)
  have hb := h.replacement_geometry S hB a hAll A hA g
  let : IsElementaryAbelian 2 B := hb.1.2.1
  let : IsElementaryAbelian 2 (Y ⊔ (B ⊓ centralizer (Y : Set H)) : Subgroup H) := hW.2.1
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_le
    (show Y ≤ Y ⊔ (B ⊓ centralizer (Y : Set H)) from le_sup_left)
  have hYS : Y ≤ S := le_sup_left.trans hW.1
  have hAB := h.replacement_commutator_centralizes_mixed S hB a hAll hF A hA g hgK hg2
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hAK : A ≤ Campbell.J (⊤ : Subgroup H) :=
    (show A ≤ Campbell.J S from le_sSup hA).trans (hST ▸ elementaryAbelianMaxJ_sylow_le_top T)
  have hout : ∀ x ∈ A, x ∉ pCore 2 H → x ∈ N := by
    intro x hx hxQ
    let : IsElementaryAbelian 2 A := hA.2.1
    have hx2 : x^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) x hx
    have hYYx := h.mixed_conjugate_actor_commutes S hB a hAll hF M hM g x hgK (hAK hx) hg2 hx2 hgM (hA.1 hx) hxQ
    have hYxS : Y.map (MulAut.conj x).toMonoidHom ≤ S := by
      rintro y ⟨z,hz,rfl⟩
      exact S.mul_mem (S.mul_mem (hA.1 hx) (hYS hz)) (S.inv_mem (hA.1 hx))
    exact commutator_normalized_of_commuting_conjugate S A B Y hAB hW x hx hYxS hYYx
  obtain ⟨t,ht,htQ⟩ := Set.not_subset.mp hAQ
  intro x hx
  by_cases hxQ : x ∈ pCore 2 H
  · have hxt : x*t ∉ pCore 2 H := by
      intro hxt
      apply htQ
      change t ∈ pCore 2 H
      simpa only [inv_mul_cancel_left] using (pCore 2 H).mul_mem ((pCore 2 H).inv_mem hxQ) hxt
    have hn := N.mul_mem (hout (x*t) (A.mul_mem hx ht) hxt) (N.inv_mem (hout t ht htQ))
    simpa only [mul_inv_cancel_right] using hn
  · exact hout x hx hxQ
end CFSG.Quasithin.ChapterC.GlaubermanNiles
