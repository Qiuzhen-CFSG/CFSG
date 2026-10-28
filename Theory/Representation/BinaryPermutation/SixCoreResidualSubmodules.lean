module

public import Theory.Representation.BinaryPermutation.SixCoreResidualMovement

/-!
# Invariant subspaces moved by a six-letter stabilizer residual

In the five-dimensional augmentation core, any subspace invariant under
the stabilizer of a nonconstant vector and moved by its literal O^{3′}
contains every displacement of that residual. For the marked pair, two
explicit 3-cycles detect movement; their displacements yield a pair in
the complementary four-set, whose conjugates span the moved three-space.
Even-permutation transport and complementation handle every nonconstant
vector. The finite checks involve only six-letter words and permutations.

The source application removes the moved-space containment premise in the
A₆-block branch of Aschbacher–Smith 13.4.8, printed p.904. It retains the
original five-space, rather than passing to its four-dimensional quotient.
-/

open Subgroup Theory.GroupTheory
namespace BinaryPermutation.SixCoreResidualSubmodules
open SixCoreResidualMovement
local instance : DecidablePred (· ∈ core (Fin 6)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype W := Subtype.fintype _
def pair : W := ⟨![1,1,0,0,0,0],by rw [mem_core];decide⟩
def a : A := ⟨Equiv.swap 2 3 * Equiv.swap 3 4,by decide⟩
def b : A := ⟨Equiv.swap 2 3 * Equiv.swap 3 5,by decide⟩
def tailPair : W := ⟨![0,0,1,1,0,0],by rw [mem_core];decide⟩
def tailPair2 : W := ⟨![0,0,1,0,1,0],by rw [mem_core];decide⟩
def tailPair3 : W := ⟨![0,0,1,0,0,1],by rw [mem_core];decide⟩
def tailEven (v : W) : Prop := v.val 0 = 0 ∧ v.val 1 = 0
instance (v : W) : Decidable (tailEven v) := inferInstanceAs (Decidable (_ ∧ _))
theorem a_stab : a ∈ S pair := by change rho a pair = pair; decide
theorem b_stab : b ∈ S pair := by change rho b pair = pair; decide
-- Every nonfixed vector yields a tail pair by one of two cubic displacements.
theorem move_pair (v : W) (hv : rho a v ≠ v ∨ rho b v ≠ v) :
    (tailEven (rho a v-v) ∧ wordWeight (rho a v-v).val = 2) ∨
    (tailEven (rho b v-v) ∧ wordWeight (rho b v-v).val = 2) := by
  revert v
  decide +kernel
-- Six explicit even permutations cover the six pairs of the complementary four-set.
def movers : Fin 6 → A := ![1,a,a*a,b,b*b,a*b]
theorem movers_stab (i : Fin 6) : movers i ∈ S pair := by
  change rho (movers i) pair = pair
  fin_cases i <;> decide
theorem move_to_pair (v : W) (h : tailEven v) (hw : wordWeight v.val = 2) :
    ∃ i : Fin 6, rho (movers i) v = tailPair := by
  revert v
  decide +kernel
theorem pair2_eq : rho (a*a) tailPair = tailPair2 := by decide
theorem pair3_eq : rho (b*b) tailPair = tailPair3 := by decide
theorem tail_span (v : W) (h : tailEven v) :
    ∃ i j k : ZMod 2, v = i • tailPair + j • tailPair2 + k • tailPair3 := by
  revert v
  decide +kernel
open Theory.SpecificGroups.SymmetricSix
private theorem pair_stabilizer : S pair = a6DuadStabilizer := by
  ext g
  change rho g pair = pair ↔ g.val ∈ duadStabilizer
  revert g
  decide +kernel
noncomputable def e : Equiv.Perm (Fin 4) ≃* S pair :=
  a6DuadModelEquiv.trans (MulEquiv.subgroupCongr pair_stabilizer.symm)
theorem model_fixed (g : Equiv.Perm (Fin 4)) (hg : signPermTwo g = 1)
    (v : W) (ha : rho a v = v) (hb : rho b v = v) : rho (e g).val v = v := by
  revert g v
  decide +kernel
theorem model_tail (g : Equiv.Perm (Fin 4)) (hg : signPermTwo g = 1)
    (v : W) : tailEven (rho (e g).val v - v) := by
  revert g v
  decide +kernel
theorem residual_sign (g : S pair) (hg : g ∈ primeToResidual 3 (S pair)) :
    signPermTwo (e.symm g) = 1 := by
  exact primeToResidual_le_ker (p := 3) (signPermTwo.comp e.symm.toMonoidHom)
    (by rw [Nat.card_eq_fintype_card]; decide) hg

theorem pair_submodule (U : Submodule (ZMod 2) W)
    (hU : ∀ g : S pair, ∀ v ∈ U, rho g.val v ∈ U)
    (hmove : ∃ g : S pair, g ∈ primeToResidual 3 (S pair) ∧
      ∃ v ∈ U, rho g.val v ≠ v) :
    ∀ g : S pair, g ∈ primeToResidual 3 (S pair) → ∀ v : W, rho g.val v-v ∈ U := by
  obtain ⟨g,hg,v,hv,hm⟩ := hmove
  have hnon : rho a v ≠ v ∨ rho b v ≠ v := by
    by_contra! hn
    apply hm
    have hh := model_fixed (e.symm g) (residual_sign g hg) v hn.1 hn.2
    simpa only [MulEquiv.apply_symm_apply] using hh
  have htail : ∃ u ∈ U, tailEven u ∧ wordWeight u.val = 2 := by
    rcases move_pair v hnon with ha | hb
    · exact ⟨_,U.sub_mem (hU ⟨a,a_stab⟩ v hv) hv,ha⟩
    · exact ⟨_,U.sub_mem (hU ⟨b,b_stab⟩ v hv) hv,hb⟩
  obtain ⟨u,hu,ht,hw⟩ := htail
  obtain ⟨i,hi⟩ := move_to_pair u ht hw
  have hp : tailPair ∈ U := hi ▸ hU ⟨movers i,movers_stab i⟩ u hu
  have hp2 : tailPair2 ∈ U := pair2_eq ▸ hU ⟨a*a,(S pair).mul_mem a_stab a_stab⟩ _ hp
  have hp3 : tailPair3 ∈ U := pair3_eq ▸ hU ⟨b*b,(S pair).mul_mem b_stab b_stab⟩ _ hp
  intro g hg v
  have ht : tailEven (rho g.val v-v) := by
    have hh := model_tail (e.symm g) (residual_sign g hg) v
    simpa only [MulEquiv.apply_symm_apply] using hh
  obtain ⟨i,j,k,he⟩ := tail_span _ ht
  rw [he]
  exact U.add_mem (U.add_mem (U.smul_mem i hp) (U.smul_mem j hp2)) (U.smul_mem k hp3)

private local instance : MulAction A W where
  smul g w := rho g w
  one_smul w := by change rho 1 w = w; rw [map_one]; rfl
  mul_smul g h w := by change rho (g*h) w = rho g (rho h w); rw [map_mul]; rfl
private theorem conjugate_action (g x : A) (v : W) :
    rho (MulAut.conj g x) (rho g v) = rho g (rho x v) := by
  change rho (g*x*g⁻¹) (rho g v) = _
  rw [← Module.End.mul_apply,← map_mul]
  simp only [mul_assoc,inv_mul_cancel,mul_one,map_mul,Module.End.mul_apply]
private theorem undo (g : A) (v : W) : rho g (rho g⁻¹ v) = v := by
  rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one]
  rfl

/-- Every invariant subspace moved by the cubic residual contains its full displacement space. -/
public theorem residual_displacements_mem (w : W) (hw : ¬ ∀ g : A, rho g w = w)
    (U : Submodule (ZMod 2) W)
    (hU : ∀ g : S w, ∀ v ∈ U, rho g.val v ∈ U)
    (hmove : ∃ g : S w, g ∈ primeToResidual 3 (S w) ∧
      ∃ v ∈ U, rho g.val v ≠ v) :
    ∀ g : S w, g ∈ primeToResidual 3 (S w) → ∀ v : W, rho g.val v-v ∈ U := by
  classical
  have hw' := not_or.mp ((not_congr (sixCore_fixed_iff w)).mp hw)
  have step (w₀ : W) (hs : S w₀ = S pair) (g : A) (hg : rho g w₀ = w) :
      ∀ x : S w, x ∈ primeToResidual 3 (S w) → ∀ v : W, rho x.val v-v ∈ U := by
    have he : (S w₀).map (MulAut.conj g).toMonoidHom = S w := by
      rw [← hg]
      exact (MulAction.stabilizer_smul_eq_stabilizer_map_conj g w₀).symm
    let f : S pair ≃* S w := (MulEquiv.subgroupCongr hs.symm).trans
      (((S w₀).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr he))
    have hf (x : S pair) : (f x).val = MulAut.conj g x.val := rfl
    have hres (x : S w) (hx : x ∈ primeToResidual 3 (S w)) :
        f.symm x ∈ primeToResidual 3 (S pair) := by
      have hh := mem_map_of_mem f.symm.toMonoidHom hx
      rwa [map_primeToResidual f.symm] at hh
    let U₀ := U.comap (rho g)
    have hU₀ : ∀ x : S pair, ∀ v ∈ U₀, rho x.val v ∈ U₀ := by
      intro x v hv
      change rho g (rho x.val v) ∈ U
      rw [← conjugate_action,← hf]
      exact hU (f x) _ hv
    have hm₀ : ∃ x : S pair, x ∈ primeToResidual 3 (S pair) ∧
        ∃ v ∈ U₀, rho x.val v ≠ v := by
      obtain ⟨x,hx,v,hv,hn⟩ := hmove
      refine ⟨f.symm x,hres x hx,rho g⁻¹ v,?_,?_⟩
      · change rho g (rho g⁻¹ v) ∈ U
        rwa [undo]
      · intro hh
        apply hn
        have hh' := congrArg (rho g) hh
        rw [← conjugate_action,← hf,MulEquiv.apply_symm_apply,undo] at hh'
        exact hh'
    have hc := pair_submodule U₀ hU₀ hm₀
    intro x hx v
    have hh := hc (f.symm x) (hres x hx) (rho g⁻¹ v)
    change rho g (rho (f.symm x).val (rho g⁻¹ v)-rho g⁻¹ v) ∈ U at hh
    rw [map_sub,← conjugate_action,← hf,MulEquiv.apply_symm_apply,undo] at hh
    exact hh
  rcases sixCore_paired_orbits pair w (by decide) (by decide) hw'.1 hw'.2 with
    ⟨g,hg⟩ | ⟨g,hg⟩
  · exact step pair rfl g hg
  · apply step (pair+sixCoreConstant) ?_ g hg
    ext x
    change rho x (pair+sixCoreConstant) = pair+sixCoreConstant ↔ rho x pair = pair
    rw [map_add,sixCoreConstant_fixed,add_left_inj]
end BinaryPermutation.SixCoreResidualSubmodules
