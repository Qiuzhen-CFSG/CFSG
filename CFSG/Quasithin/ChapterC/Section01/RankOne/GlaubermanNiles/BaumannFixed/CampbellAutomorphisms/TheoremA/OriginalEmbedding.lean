module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.Source
/-!
# Campbell Theorem A for an arbitrary original marking

Restrict the marking to its literal range and conjugate its automorphisms
through that equivalence. Injective Baumann transport supplies the range
hypothesis; the exact image identity retains the original maps in the
commutator conclusion. Source: Campbell II.7 and its C.1.18 application.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H]

omit [Finite B] [Finite H] in
private theorem range_automorphism_image (e : B →* H) (he : Function.Injective e)
    (a : MulAut B) (X : Subgroup H) :
    automorphismImage e.range (MulAut.congr (MonoidHom.ofInjective he) a) X =
      ((X.comap e).map a.toMonoidHom).map e := by
  let c := MonoidHom.ofInjective he
  apply le_antisymm
  · rintro z ⟨v,⟨w,hw,rfl⟩,rfl⟩
    refine ⟨a (c.symm w),⟨c.symm w,?_,rfl⟩,?_⟩
    · change e (c.symm w) ∈ X
      rwa [MonoidHom.apply_ofInjective_symm]
    · change e (a (c.symm w)) = (c (a (c.symm w)) : H)
      rfl
  · rintro z ⟨v,⟨w,hw,rfl⟩,rfl⟩
    refine ⟨(MulAut.congr c a) (c w),⟨c w,?_,rfl⟩,?_⟩
    · exact hw
    · change (c (a (c.symm (c w))) : H)=e (a w)
      rw [c.symm_apply_apply]
      rfl

theorem InLocalClass.campbell_theoremA_original
    {e : B →* H} (h : InLocalClass e) (hB : IsBaumannFixed B)
    (hAll : ∀ a : MulAut B, ((Campbell.V H).comap e |>.map a.toMonoidHom).map e ≤ pCore 2 H) :
    ∀ a : MulAut B,
      ⁅Campbell.J (⊤ : Subgroup H),((Campbell.F H).comap e |>.map a.toMonoidHom).map e⁆ ≤ Campbell.F H := by
  let c := MonoidHom.ofInjective h.injective
  have he : e.comp c.symm.toMonoidHom = e.range.subtype := by
    ext x
    exact MonoidHom.apply_ofInjective_symm h.injective x
  have hS : InLocalClass e.range.subtype := he ▸ h.precomp_equiv c.symm
  have hBS : IsBaumannFixed e.range := by
    have hm := baumann_map_injective c.toMonoidHom c.injective (⊤ : Subgroup B)
    change (ChapterB.baumann (⊤ : Subgroup B)).map c.toMonoidHom =
      ChapterB.baumann ((⊤ : Subgroup B).map c.toMonoidHom) at hm
    have ht : (⊤ : Subgroup B).map c.toMonoidHom=⊤ :=
      (MonoidHom.range_eq_map c.toMonoidHom).symm.trans (MonoidHom.range_eq_top.mpr c.surjective)
    rw [show ChapterB.baumann (⊤ : Subgroup B)=⊤ from hB,ht] at hm
    exact hm.symm
  have hall : ∀ a : MulAut e.range, automorphismImage e.range a (Campbell.V H) ≤ pCore 2 H := by
    intro a
    obtain ⟨b,rfl⟩ := (MulAut.congr c).surjective a
    rw [range_automorphism_image]
    exact hAll b
  intro a
  have hh := hS.campbell_theoremA e.range hBS hall (MulAut.congr c a)
  rwa [range_automorphism_image] at hh
end CFSG.Quasithin.ChapterC.GlaubermanNiles
