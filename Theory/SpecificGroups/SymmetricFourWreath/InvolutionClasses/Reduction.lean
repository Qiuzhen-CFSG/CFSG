module
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.Factor

/-!
# Reducing local involutions to B or the swapping class

An involution outside the wreath base is conjugate to the pure swap by an
explicit base element. Inside the base, the small S4 certificate conjugates
each coordinate into the marked nonnormal Klein four. This supplies the
literal class-cover input of the source transfer argument without enumerating
conjugating pairs in the order-1152 wreath product.

Source: Aschbacher–Smith 13.9.3–4, printed p.970.
-/

public section
namespace SymmetricFourWreath.InvolutionClasses
open Subgroup

theorem outside_involution_conjugate (x : W) (hx : x.right ≠ 1) (hxx : x*x=1) :
    IsConj swap x := by
  have hr : x.right=turn := (c2_eq_one_or_turn x.right).resolve_left hx
  have he : x.left 1*x.left turn=1 := by
    have hh := congrArg (fun w:W=>w.left 1) hxx
    simpa [hr] using hh
  have hl : (x.left 1)⁻¹=x.left turn := (inv_eq_iff_mul_eq_one).mpr he
  let a : W := ⟨fun i=>if i=1 then x.left 1 else 1,1⟩
  apply isConj_iff.mpr
  refine ⟨a,?_⟩
  apply RegularWreathProduct.ext
  · funext q
    rcases c2_eq_one_or_turn q with rfl|rfl
    · simp [a,swap,turn_ne_one]
    · simp [a,swap,turn_ne_one,hl]
  · simpa [a,swap] using hr.symm

theorem base_involution_conjugate_mem_B (x : W) (hx : x.right=1) (hxx : x*x=1) :
    ∃ g : W,g*x*g⁻¹∈B := by
  have hi (i : C2) : x.left i*x.left i=1 := by
    have h := congrArg (fun w:W=>w.left i) hxx
    simpa [hx] using h
  choose a ha using fun i=>factor_involution_representative (x.left i) (hi i)
  let g : W := ⟨a,1⟩
  refine ⟨g,(mem_elementary false false _).mpr ⟨?_,?_,?_⟩⟩
  · simp [hx,g]
  · rw [conjugate_left g x hx]
    simp only [g,inv_one,one_mul]
    rw [ha]
    exact factor_representative_mem_plane _
  · rw [conjugate_left g x hx]
    simp only [g,inv_one,one_mul]
    rw [ha]
    exact factor_representative_mem_plane _

theorem involution_cover (x : W) (hxx : x*x=1) :
    IsConj swap x ∨ ∃g:W,g*x*g⁻¹∈B := by
  by_cases hx:x.right=1
  · exact Or.inr (base_involution_conjugate_mem_B x hx hxx)
  · exact Or.inl (outside_involution_conjugate x hx hxx)

theorem swap_conjugate_not_mem_J (g : W) : g*swap*g⁻¹∉J := by
  intro h
  have hr := ((mem_J _).mp h).1
  have he : (g*swap*g⁻¹).right=turn := by simp [swap,mul_comm]
  exact turn_ne_one (he.symm.trans hr)

end SymmetricFourWreath.InvolutionClasses
