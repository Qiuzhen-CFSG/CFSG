module

public import Theory.Representation.G2BinaryIsotropicThree.Words
public import Theory.Representation.G2NaturalBinary

/-!
# The source dichotomy for binary isotropic three-spaces

Move a nonzero vector by the actual derived group, then use the fifteen-plane
normalization and the checked octonion words. The distinguished case remains
inside G₂(2)′. In the other case octonion generation proves the full pointwise
stabilizer trivial. The conclusion covers both faithful derived-group orbits;
it does not assert that the derived group has only two three-space orbits.

Source: Aschbacher–Smith 13.3.12(3), printed p.890.
-/

public section

open Atlas.SplitOctonion Module Submodule Subgroup
namespace Atlas.G2.Natural.BinaryIsotropicThree
open BinaryNondegeneratePlane Atlas.G2.Restricted.NaturalCoordinates

private theorem finrank_map_action (P : Submodule K W) (g : Model K) :
    finrank K (P.map (rho g))=finrank K P :=
  (LinearEquiv.ofBijective (rho g) (rho.apply_bijective g)).finrank_map_eq P

private theorem move_to_first (v : W) (hv : v≠0) :
    ∃g : commutator (Model K),rho g.val v=firstVector := by
  have hv' : (equiv K).symm v≠0 := fun hh=>hv ((equiv K).symm.map_eq_zero_iff.mp hh)
  have hf : (equiv K).symm firstVector≠0 := by
    intro hh
    have h := congrFun ((equiv K).symm.map_eq_zero_iff.mp hh) 0
    exact one_ne_zero h
  obtain ⟨g,hg⟩ := Binary.natural_transitive hv' hf
  refine ⟨g,?_⟩
  change equiv K (Natural.action K g.val ((equiv K).symm v))=firstVector
  rw [show Natural.action K g.val ((equiv K).symm v)=(equiv K).symm firstVector from hg]
  exact (equiv K).apply_symm_apply firstVector

/-- The exact source dichotomy: the distinguished derived-group orbit, or
trivial pointwise stabilizer in the full octonion group. -/
theorem derived_orbit_or_pointwise_faithful (P : Submodule K W)
    (hi : ∀v∈P,∀w∈P,form v w=0) (hd : finrank K P=3) :
    (∃g : commutator (Model K),P.map (rho g.val)=target false) ∨
      ∀h : Model K,(∀v∈P,rho h v=v)→h=1 := by
  have hn : P≠⊥ := by intro h;rw [h,finrank_bot] at hd;omega
  obtain ⟨v,hv,hv0⟩ := P.ne_bot_iff.mp hn
  obtain ⟨g,hg⟩ := move_to_first v hv0
  let P₁ := P.map (rho g.val)
  have hfirst : firstVector∈P₁ := ⟨v,hv,hg⟩
  have hi₁ : ∀v∈P₁,∀w∈P₁,form v w=0 := by
    rintro x ⟨u,hu,rfl⟩ y ⟨v,hv,rfl⟩
    rw [form_invariant]
    exact hi u hu v hv
  have hd₁ : finrank K P₁=3 := (finrank_map_action P g.val).trans hd
  obtain ⟨i,hPi⟩ := exists_markedPlane P₁ hfirst hi₁ hd₁
  let a := word (Certificate.words i)
  have hmap : P₁.map (rho a)≤target (Certificate.other i) :=
    (Submodule.map_mono hPi).trans (markedPlane_map_le i)
  have heq : P₁.map (rho a)=target (Certificate.other i) :=
    Submodule.eq_of_le_of_finrank_eq hmap
      ((finrank_map_action P₁ a).trans (hd₁.trans (finrank_target _).symm))
  have hcomp : P.map (rho (a*g.val))=target (Certificate.other i) := by
    rw [show rho (a*g.val)=(rho a).comp (rho g.val) by rw [map_mul];rfl]
    rw [Submodule.map_comp]
    exact heq
  cases hb : Certificate.other i
  · left
    have ha : a∈commutator (Model K) := word_mem_derived _ (Certificate.derived_words i hb)
    refine ⟨⟨a*g.val,(commutator (Model K)).mul_mem ha g.property⟩,?_⟩
    simpa only [hb] using hcomp
  · right
    intro h hfix
    let c := a*g.val
    have hconj : ∀v∈target true,rho (c*h*c⁻¹) v=v := by
      intro v hv
      have hv' : v∈P.map (rho c) := by simpa only [c,hcomp,hb] using hv
      obtain ⟨u,hu,rfl⟩ := hv'
      simp only [map_mul,Module.End.mul_apply]
      rw [rho.inv_self_apply,hfix u hu]
    have he : c*h*c⁻¹=1 := eq_one_of_fixes_other _ hconj
    have he' : c*h=c := mul_inv_eq_one.mp he
    exact mul_left_cancel (he'.trans (mul_one c).symm)
end Atlas.G2.Natural.BinaryIsotropicThree
