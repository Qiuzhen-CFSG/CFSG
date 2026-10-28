module
public import Theory.GroupAction.C4SquareCubicBasis
public import Mathlib.GroupTheory.Perm.Fin
/-!
# Uniqueness of the faithful S₃ action on C₄ × C₄

For each action, a cubic element and its inverting involution admit a
basis swapped by the involution. The cubic norm is one because the cubic
has no fixed point. A marked change of basis therefore intertwines both
S₃ generators, hence the whole action. This is the action comparison in
the abelian local vertex of F.1.12(I)(8), printed p.263.
-/
public section
namespace C4SquareExtension.SymmetricThreeActions
open Subgroup
abbrev V := Model
abbrev S3 := Equiv.Perm (Fin 3)
private def c : S3 := Equiv.swap 0 1 * Equiv.swap 1 2
private def t : S3 := Equiv.swap 0 1
private theorem c3 : c^3=1 := by decide
private theorem cne : c≠1 := by decide
private theorem t2 : t^2=1 := by decide
private theorem tct : t*c*t=c^2 := by decide
private theorem generated : closure ({c,t} : Set S3)=⊤ := by
  have hall : ∀s : S3, s=1 ∨ s=c ∨ s=c^2 ∨ s=t ∨ s=c*t ∨ s=c^2*t := by decide
  apply top_unique
  intro s _
  have hc : c∈closure ({c,t} : Set S3) := subset_closure (by simp)
  have ht : t∈closure ({c,t} : Set S3) := subset_closure (by simp)
  rcases hall s with rfl|rfl|rfl|rfl|rfl|rfl
  · exact one_mem _
  · exact hc
  · exact pow_mem hc 2
  · exact ht
  · exact mul_mem hc ht
  · exact mul_mem (pow_mem hc 2) ht
private theorem norm_one (a : MulAut V) (ha:a^3=1) (hne:a≠1) (x:V) :
    a (a x)=(x*a x)⁻¹ := by
  have h3 : a (a (a x))=x := by
    simpa only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply] using DFunLike.congr_fun ha x
  apply eq_inv_of_mul_eq_one_right
  apply Cubic.fixed_free a ha hne
  simp only [map_mul,h3]
  ac_rfl
private theorem action_data (ρ : S3 →* MulAut V) (hf : Function.Injective ρ) :
    (ρ c)^3=1 ∧ ρ c≠1 ∧ (ρ t)^2=1 ∧
    ∀x, ρ t (ρ c (ρ t x))=ρ c (ρ c x) := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [←map_pow,c3,map_one]
  · intro h
    exact cne (hf (h.trans (map_one _).symm))
  · rw [←map_pow,t2,map_one]
  · intro x
    have h := DFunLike.congr_fun (congrArg ρ tct) x
    simpa only [map_mul,map_pow,pow_two,MulAut.mul_apply] using h

theorem exists_equivariant (ρ σ : S3 →* MulAut V)
    (hr : Function.Injective ρ) (hs : Function.Injective σ) :
    ∃f : MulAut V, ∀s x, f (ρ s x)=σ s (f x) := by
  obtain ⟨ha,hn,hb,hba⟩ := action_data ρ hr
  obtain ⟨ha',hn',hb',hba'⟩ := action_data σ hs
  obtain ⟨x,hx,hbx,hgen⟩ := Cubic.exists_swap_basis (ρ c) (ρ t) ha hn hb hba
  obtain ⟨y,hy,hby,_⟩ := Cubic.exists_swap_basis (σ c) (σ t) ha' hn' hb' hba'
  obtain ⟨f,hfx,hfax⟩ := Cubic.exists_equiv_of_good_bases x (ρ c x) y (σ c y) hx hy
  have htfix : ρ t (ρ c x)=x := by
    rw [←hbx]
    simpa only [pow_two,MulAut.mul_apply,MulAut.one_apply] using DFunLike.congr_fun hb x
  have htfix' : σ t (σ c y)=y := by
    rw [←hby]
    simpa only [pow_two,MulAut.mul_apply,MulAut.one_apply] using DFunLike.congr_fun hb' y
  have hc (z:V) : f (ρ c z)=σ c (f z) := by
    have he : f.toMonoidHom.comp (ρ c).toMonoidHom=(σ c).toMonoidHom.comp f.toMonoidHom := by
      apply MonoidHom.eq_of_eqOn_dense hgen
      intro z hz
      rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hz : z=x∨z=ρ c x) with hz|hz
      · subst z
        change f (ρ c x)=σ c (f x)
        rw [hfx,hfax]
      · subst z
        change f (ρ c (ρ c x))=σ c (f (ρ c x))
        rw [norm_one (ρ c) ha hn,map_inv,map_mul,hfx,hfax,norm_one (σ c) ha' hn']
    exact DFunLike.congr_fun he z
  have ht (z:V) : f (ρ t z)=σ t (f z) := by
    have he : f.toMonoidHom.comp (ρ t).toMonoidHom=(σ t).toMonoidHom.comp f.toMonoidHom := by
      apply MonoidHom.eq_of_eqOn_dense hgen
      intro z hz
      rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hz : z=x∨z=ρ c x) with hz|hz
      · subst z
        change f (ρ t x)=σ t (f x)
        rw [hbx,hfax,hfx,hby]
      · subst z
        change f (ρ t (ρ c x))=σ t (f (ρ c x))
        rw [htfix,hfx,hfax,htfix']
    exact DFunLike.congr_fun he z
  have he : (MulAut.congr f).toMonoidHom.comp ρ=σ := by
    apply MonoidHom.eq_of_eqOn_dense generated
    intro s hs
    rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hs : s=c∨s=t) with rfl|rfl
    · apply MulEquiv.ext
      intro z
      change f (ρ c (f.symm z))=σ c z
      rw [hc,MulEquiv.apply_symm_apply]
    · apply MulEquiv.ext
      intro z
      change f (ρ t (f.symm z))=σ t z
      rw [ht,MulEquiv.apply_symm_apply]
  refine ⟨f,?_⟩
  intro s z
  have hh := DFunLike.congr_fun (DFunLike.congr_fun he s) (f z)
  simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.congr_apply,
    MulEquiv.trans_apply,MulEquiv.symm_apply_apply] using hh
end C4SquareExtension.SymmetricThreeActions
