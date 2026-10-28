module
public import Theory.Representation.BinaryPermutation.SixCoreResidualMovement

/-!
# Fixing a residual layer in the six-letter core

A moving linear map normalizing the alternating six-letter action and
fixing the complementary residual layer forces the all-one vector into
any subspace containing that layer and its displacements. A fixed weight-two
vector makes the whole weight-two orbit invariant. Four elementary weight
tests then determine the image of the one remaining basis vector. This
avoids classifying the entire linear normalizer. Conjugation and
complementation transport the marked-pair argument to every nonconstant
vector in the original five-dimensional augmentation core.

Source: Aschbacher–Smith 13.4.8, printed p.904, the equal-layer case.
The actual common-normalizer application is in ShortLayerFixedLine.
-/

open Subgroup Theory.GroupTheory
namespace BinaryPermutation.SixCoreFixedLayer
open SixCoreResidualMovement
local instance : DecidablePred (· ∈ core (Fin 6)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype W := Subtype.fintype _
private def pair : W := ⟨![1,1,0,0,0,0],by rw [mem_core];decide⟩
private def a : A := ⟨Equiv.swap 2 3 * Equiv.swap 3 4,by decide⟩
private def b : A := ⟨Equiv.swap 2 3 * Equiv.swap 3 5,by decide⟩
private def p : W := ⟨![0,0,1,1,0,0],by rw [mem_core];decide⟩
private def q : W := ⟨![0,0,1,0,1,0],by rw [mem_core];decide⟩
private def r : W := ⟨![0,0,1,0,0,1],by rw [mem_core];decide⟩
private def t : W := ⟨![1,0,1,0,0,0],by rw [mem_core];decide⟩
private theorem a_stab : a ∈ S pair := by change rho a pair = pair; decide
private theorem b_stab : b ∈ S pair := by change rho b pair = pair; decide
private theorem a_res : (⟨a,a_stab⟩ : S pair) ∈ primeToResidual 3 (S pair) :=
  mem_primeToResidual_of_pow (n := 1) (by decide)
private theorem b_res : (⟨b,b_stab⟩ : S pair) ∈ primeToResidual 3 (S pair) :=
  mem_primeToResidual_of_pow (n := 1) (by decide)
private theorem p_move : rho a t-t = p := by decide
private theorem q_move : rho (a*a) t-t = q := by decide
private theorem r_move : rho (b*b) t-t = r := by decide
private theorem pair_sum : pair = sixCoreConstant + p + q + r := by decide
private theorem constant_sum : sixCoreConstant = pair + p + q + r := by decide
private theorem spanning (v : W) : ∃ i j k l m : ZMod 2,
    v = i • p + j • q + k • r + l • sixCoreConstant + m • t := by
  revert v
  decide +kernel
private theorem weight_detection (v : W)
    (hv : wordWeight v.val = 2) (hp : wordWeight (v+p).val = 2)
    (hq : wordWeight (v+q).val = 2) (hr : wordWeight (v+r).val = 2)
    (hd : wordWeight (v+pair).val = 2) : v = t ∨ v = t+pair := by
  revert v
  decide +kernel

private theorem pair_constant_mem
    (N : Submodule (ZMod 2) W) (u : W →ₗ[ZMod 2] W)
    (hN : ∀ x : S pair, x ∈ primeToResidual 3 (S pair) → ∀ v : W,
      rho x.val v-v ∈ N)
    (hf : ∀ x : S pair, x ∈ primeToResidual 3 (S pair) → ∀ v : W,
      u (rho x.val v-v) = rho x.val v-v)
    (hd : u sixCoreConstant = sixCoreConstant)
    (hn : ∀ a : A, ∃ b : A, ∀ v : W, u (rho a v) = rho b (u v))
    (hne : ∃ v : W, u v ≠ v)
    (hm : ∀ v : W, u v-v ∈ N) : sixCoreConstant ∈ N := by
  have hp : p ∈ N := p_move ▸ hN ⟨a,a_stab⟩ a_res t
  have hq : q ∈ N := q_move ▸ hN _ ((primeToResidual 3 (S pair)).mul_mem a_res a_res) t
  have hr : r ∈ N := r_move ▸ hN _ ((primeToResidual 3 (S pair)).mul_mem b_res b_res) t
  have hup : u p = p := p_move ▸ hf ⟨a,a_stab⟩ a_res t
  have huq : u q = q := q_move ▸ hf _ ((primeToResidual 3 (S pair)).mul_mem a_res a_res) t
  have hur : u r = r := r_move ▸ hf _ ((primeToResidual 3 (S pair)).mul_mem b_res b_res) t
  have hud : u pair = pair := by rw [pair_sum,map_add,map_add,map_add,hd,hup,huq,hur]
  have hw (v : W) (hv : wordWeight v.val = 2) : wordWeight (u v).val = 2 := by
    obtain ⟨g,hg⟩ := exists_even_permutation_of_weight (by decide : 2 < Fintype.card (Fin 6))
      p.val v.val (by simpa only [show wordWeight p.val = 2 by decide] using hv.symm)
    have hgv : rho g p = v := Subtype.ext hg
    obtain ⟨b,hb⟩ := hn g
    rw [← hgv,hb,hup]
    exact (wordWeight_permute b.val p.val).trans (by decide)
  have hcases : u t = t ∨ u t = t+pair := weight_detection (u t)
    (hw t (by decide))
    (by simpa only [map_add,hup] using hw (t+p) (by decide))
    (by simpa only [map_add,huq] using hw (t+q) (by decide))
    (by simpa only [map_add,hur] using hw (t+r) (by decide))
    (by simpa only [map_add,hud] using hw (t+pair) (by decide))
  rcases hcases with ht | ht
  · obtain ⟨v,hv⟩ := hne
    obtain ⟨i,j,k,l,m,he⟩ := spanning v
    apply False.elim
    apply hv
    rw [he,map_add,map_add,map_add,map_add,map_smul,map_smul,map_smul,map_smul,map_smul,
      hup,huq,hur,hd,ht]
  · have hpair : pair ∈ N := by
      have hh := hm t
      rwa [ht,add_sub_cancel_left] at hh
    rw [constant_sum]
    exact N.add_mem (N.add_mem (N.add_mem hpair hp) hq) hr
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

/-- A moving normalizer which fixes the residual layer forces the constant
line into any subspace containing that layer and all its displacements. -/
public theorem constant_mem_of_fixed_residual_layer (w : W)
    (hw : ¬ ∀ g : A, rho g w = w)
    (N : Submodule (ZMod 2) W) (u : W →ₗ[ZMod 2] W)
    (hN : ∀ x : S w, x ∈ primeToResidual 3 (S w) → ∀ v : W,
      rho x.val v-v ∈ N)
    (hf : ∀ x : S w, x ∈ primeToResidual 3 (S w) → ∀ v : W,
      u (rho x.val v-v) = rho x.val v-v)
    (hd : u sixCoreConstant = sixCoreConstant)
    (hn : ∀ a : A, ∃ b : A, ∀ v : W, u (rho a v) = rho b (u v))
    (hne : ∃ v : W, u v ≠ v)
    (hm : ∀ v : W, u v-v ∈ N) : sixCoreConstant ∈ N := by
  classical
  have hw' := not_or.mp ((not_congr (sixCore_fixed_iff w)).mp hw)
  have step (w₀ : W) (hs : S w₀ = S pair) (g : A) (hg : rho g w₀ = w) :
      sixCoreConstant ∈ N := by
    have he : (S w₀).map (MulAut.conj g).toMonoidHom = S w := by
      rw [← hg]
      exact (MulAction.stabilizer_smul_eq_stabilizer_map_conj g w₀).symm
    let f : S pair ≃* S w := (MulEquiv.subgroupCongr hs.symm).trans
      (((S w₀).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr he))
    have hval (x : S pair) : (f x).val = MulAut.conj g x.val := rfl
    have hres (x : S pair) (hx : x ∈ primeToResidual 3 (S pair)) :
        f x ∈ primeToResidual 3 (S w) := by
      rw [← map_primeToResidual f]
      exact mem_map_of_mem f.toMonoidHom hx
    let N₀ := N.comap (rho g)
    let u₀ : W →ₗ[ZMod 2] W := (rho g⁻¹).comp (u.comp (rho g))
    have hN₀ : ∀ x : S pair, x ∈ primeToResidual 3 (S pair) → ∀ v : W,
        rho x.val v-v ∈ N₀ := by
      intro x hx v
      have hh := hN (f x) (hres x hx) (rho g v)
      rw [hval,conjugate_action,← map_sub] at hh
      exact hh
    have hf₀ : ∀ x : S pair, x ∈ primeToResidual 3 (S pair) → ∀ v : W,
        u₀ (rho x.val v-v) = rho x.val v-v := by
      intro x hx v
      have hh := hf (f x) (hres x hx) (rho g v)
      rw [hval,conjugate_action,← map_sub] at hh
      change rho g⁻¹ (u (rho g (rho x.val v-v))) = _
      rw [hh,← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one]
      rfl
    have hd₀ : u₀ sixCoreConstant = sixCoreConstant := by
      change rho g⁻¹ (u (rho g sixCoreConstant)) = _
      rw [sixCoreConstant_fixed,hd,sixCoreConstant_fixed]
    have hn₀ : ∀ a : A, ∃ b : A, ∀ v : W, u₀ (rho a v) = rho b (u₀ v) := by
      intro a
      obtain ⟨b,hb⟩ := hn (MulAut.conj g a)
      refine ⟨MulAut.conj g⁻¹ b,fun v => ?_⟩
      change rho g⁻¹ (u (rho g (rho a v))) =
        rho (MulAut.conj g⁻¹ b) (rho g⁻¹ (u (rho g v)))
      rw [← conjugate_action g a,hb,conjugate_action]
    have hne₀ : ∃ v : W, u₀ v ≠ v := by
      obtain ⟨v,hv⟩ := hne
      refine ⟨rho g⁻¹ v,fun hh => hv ?_⟩
      have h := congrArg (rho g) hh
      change rho g (rho g⁻¹ (u (rho g (rho g⁻¹ v)))) = rho g (rho g⁻¹ v) at h
      simpa only [undo] using h
    have hm₀ : ∀ v : W, u₀ v-v ∈ N₀ := by
      intro v
      change rho g (rho g⁻¹ (u (rho g v))-v) ∈ N
      rw [map_sub,undo]
      exact hm (rho g v)
    have hh := pair_constant_mem N₀ u₀ hN₀ hf₀ hd₀ hn₀ hne₀ hm₀
    change rho g sixCoreConstant ∈ N at hh
    rwa [sixCoreConstant_fixed] at hh
  rcases sixCore_paired_orbits pair w (by decide) (by decide) hw'.1 hw'.2 with
    ⟨g,hg⟩ | ⟨g,hg⟩
  · exact step pair rfl g hg
  · apply step (pair+sixCoreConstant) ?_ g hg
    ext y
    change rho y (pair+sixCoreConstant) = pair+sixCoreConstant ↔ rho y pair = pair
    rw [map_add,sixCoreConstant_fixed,add_left_inj]

end BinaryPermutation.SixCoreFixedLayer
