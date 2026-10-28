module
public import Theory.Representation.BinaryPermutation.SixCoreResidualMovement
public import Theory.Representation.BinaryOffender.CommutingPerfectSupports

/-!
# The residual three-space at a weight-four augmentation vector

In the six-letter binary augmentation core, the cubic residual of a vector
stabilizer moves an eight-element subspace avoiding the constant word. Its
two-core moves this subspace only along the weight-four vector. The marked
calculation uses the complementary A₄ and its Klein four subgroup; actual
even permutations transport the residual, two-core and displacement spaces.

This is the module calculation used in the last paragraph of the mixed-pair
exclusion, Aschbacher–Smith 13.4.15, printed p.912, refs/quasithin.pdf.
The original-group application is Nonsolvable.WeightFourResidual.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace BinaryPermutation.SixCoreResidualLine
open SixCoreResidualMovement
open Theory.SpecificGroups.SymmetricSix (a6DuadStabilizer duadStabilizer a6DuadModelEquiv signPermTwo)
local instance : DecidablePred (· ∈ core (Fin 6)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype W := Subtype.fintype _

private def pair : W := ⟨![1,1,0,0,0,0],by rw [mem_core];decide⟩
private def a : A := ⟨Equiv.swap 2 3 * Equiv.swap 3 4,by decide⟩
private def b : A := ⟨Equiv.swap 2 3 * Equiv.swap 3 5,by decide⟩
private def tailPair : W := ⟨![0,0,1,1,0,0],by rw [mem_core];decide⟩
private def tailPair2 : W := ⟨![0,0,1,0,1,0],by rw [mem_core];decide⟩
private def tailPair3 : W := ⟨![0,0,1,0,0,1],by rw [mem_core];decide⟩
private def tailEven (v : W) : Prop := v.val 0 = 0 ∧ v.val 1 = 0
private instance (v : W) : Decidable (tailEven v) := inferInstanceAs (Decidable (_ ∧ _))
private theorem a_stab : a ∈ S pair := by change rho a pair = pair; decide
private theorem b_stab : b ∈ S pair := by change rho b pair = pair; decide
private theorem tail_span (v : W) (h : tailEven v) :
    ∃ i j k : ZMod 2, v = i • tailPair + j • tailPair2 + k • tailPair3 := by
  revert v
  decide +kernel
private theorem pair_stabilizer : S pair = a6DuadStabilizer := by
  ext g
  change rho g pair = pair ↔ g.val ∈ duadStabilizer
  revert g
  decide +kernel
private noncomputable def e : Equiv.Perm (Fin 4) ≃* S pair :=
  a6DuadModelEquiv.trans (MulEquiv.subgroupCongr pair_stabilizer.symm)
private theorem model_tail (g : Equiv.Perm (Fin 4)) (hg : signPermTwo g = 1)
    (v : W) : tailEven (rho (e g).val v - v) := by
  revert g v
  decide +kernel
private theorem residual_sign (g : S pair) (hg : g ∈ primeToResidual 3 (S pair)) :
    signPermTwo (e.symm g) = 1 := by
  exact primeToResidual_le_ker (p := 3) (signPermTwo.comp e.symm.toMonoidHom)
    (by rw [Nat.card_eq_fintype_card]; decide) hg

@[expose] def residual (w : W) : Subgroup A := (primeToResidual 3 (S w)).map (S w).subtype
@[expose] def moved (w : W) : Submodule (ZMod 2) W := subspaceCommutator rho ⊤ (residual w)
private def tailSpace : Submodule (ZMod 2) W where
  carrier := {v | tailEven v}
  zero_mem' := ⟨rfl,rfl⟩
  add_mem' := by rintro v w ⟨hv0,hv1⟩ ⟨hw0,hw1⟩; exact ⟨by simp [hv0,hw0],by simp [hv1,hw1]⟩
  smul_mem' := by rintro c v ⟨hv0,hv1⟩; exact ⟨by simp [hv0],by simp [hv1]⟩

private theorem pair_moved : moved pair = tailSpace := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨g,hg,rfl⟩,v,_,rfl⟩
    have ht := model_tail (e.symm g) (residual_sign g hg) v
    change tailEven (rho g.val v-v)
    simpa only [MulEquiv.apply_symm_apply] using ht
  · have hc (g : S pair) (hg : g ∈ primeToResidual 3 (S pair)) (v : W) :
        rho g.val v-v ∈ moved pair :=
      Submodule.subset_span ⟨g.val,mem_map_of_mem _ hg,v,Submodule.mem_top,rfl⟩
    let t : W := ⟨![1,0,1,0,0,0],by rw [mem_core];decide⟩
    have ha : (⟨a,a_stab⟩ : S pair) ∈ primeToResidual 3 (S pair) :=
      mem_primeToResidual_of_pow (n := 1) (by decide)
    have hb : (⟨b,b_stab⟩ : S pair) ∈ primeToResidual 3 (S pair) :=
      mem_primeToResidual_of_pow (n := 1) (by decide)
    have hp : tailPair ∈ moved pair := (show rho a t-t = tailPair by decide) ▸ hc _ ha t
    have hq : tailPair2 ∈ moved pair := (show rho (a*a) t-t = tailPair2 by decide) ▸
      hc _ ((primeToResidual 3 (S pair)).mul_mem ha ha) t
    have hr : tailPair3 ∈ moved pair := (show rho (b*b) t-t = tailPair3 by decide) ▸
      hc _ ((primeToResidual 3 (S pair)).mul_mem hb hb) t
    intro v hv
    obtain ⟨i,j,k,he⟩ := tail_span v hv
    rw [he]
    exact (moved pair).add_mem ((moved pair).add_mem ((moved pair).smul_mem i hp)
      ((moved pair).smul_mem j hq)) ((moved pair).smul_mem k hr)

private theorem pair_core_displacement (g : Equiv.Perm (Fin 4))
    (hg : g.sign = 1 ∧ g^2 = 1) (v : W) (hv : tailEven v) :
    rho (e g).val v-v = 0 ∨ rho (e g).val v-v = pair+sixCoreConstant := by
  revert g v
  decide +kernel

private theorem pair_double_le :
    subspaceCommutator rho (moved pair) ((residual pair).pCoreIn 2) ≤
      Submodule.span (ZMod 2) ({pair+sixCoreConstant} : Set W) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,v,hv,rfl⟩
  rw [residual,←map_pCoreIn_of_injective 2 _ _ (S pair).subtype_injective] at hg
  obtain ⟨b,hb,rfl⟩ := hg
  obtain ⟨c,hc,he⟩ := hb
  have hc' : c.val ∈ pCore 2 (S pair) := by
    rwa [pCore_eq_comap_of_normal] at hc
  have hb' : b ∈ pCore 2 (S pair) := he ▸ hc'
  have hek : e.symm b ∈ pCore 2 (Equiv.Perm (Fin 4)) := by
    rw [←pCore_map_iso 2 e.symm]
    exact mem_map_of_mem _ hb'
  rw [←Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq,Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_mem_iff] at hek
  rw [pair_moved] at hv
  have hd := pair_core_displacement (e.symm b) hek v hv
  simp only [MulEquiv.apply_symm_apply] at hd
  change rho b.val v-v ∈ Submodule.span (ZMod 2) ({pair+sixCoreConstant} : Set W)
  rcases hd with hd | hd
  · rw [hd]; exact Submodule.zero_mem _
  · rw [hd]; exact Submodule.subset_span rfl

private local instance : MulAction A W where
  smul g w := rho g w
  one_smul w := by change rho 1 w = w; rw [map_one]; rfl
  mul_smul g h w := by change rho (g*h) w = rho g (rho h w); rw [map_mul]; rfl

private theorem residual_conjugate (g : A) (w : W) :
    (residual w).map (MulAut.conj g).toMonoidHom = residual (rho g w) := by
  rw [residual,map_embedded_primeToResidual_of_hom]
  have hs : (S w).map (MulAut.conj g).toMonoidHom = S (rho g w) :=
    (MulAction.stabilizer_smul_eq_stabilizer_map_conj g w).symm
  exact congrArg (fun P : Subgroup A => (primeToResidual 3 P).map P.subtype) hs

private theorem moved_conjugate (g : A) (w : W) :
    (moved w).map (rho g) = moved (rho g w) := by
  rw [moved,subspaceCommutator_map_conj,Submodule.map_top,
    LinearMap.range_eq_top.mpr (rho.apply_bijective g).surjective,residual_conjugate]
  rfl

private theorem four_residual : residual (pair+sixCoreConstant) = residual pair := by
  have hs : S (pair+sixCoreConstant) = S pair := by
    ext x
    change rho x (pair+sixCoreConstant) = pair+sixCoreConstant ↔ rho x pair = pair
    rw [map_add,sixCoreConstant_fixed,add_left_inj]
  exact congrArg (fun P : Subgroup A => (primeToResidual 3 P).map P.subtype) hs

private theorem pair_card : Nat.card (moved pair) = 8 := by
  rw [pair_moved]
  let : DecidablePred (· ∈ tailSpace) := fun v => inferInstanceAs (Decidable (tailEven v))
  let : Fintype tailSpace := Subtype.fintype _
  rw [Nat.card_eq_fintype_card]
  decide

private theorem pair_not_constant : sixCoreConstant ∉ moved pair := by
  rw [pair_moved]
  intro h
  have : (1 : ZMod 2) = 0 := h.1
  exact one_ne_zero this

/-- The literal residual moves a three-space avoiding the constant line. Its
 two-core moves that space only along the original weight-four vector. -/
theorem weight_four_residual (w : W) (hw : wordWeight w.val = 4) :
    Nat.card (moved w) = 8 ∧ sixCoreConstant ∉ moved w ∧
      subspaceCommutator rho (moved w) ((residual w).pCoreIn 2) ≤
        Submodule.span (ZMod 2) ({w} : Set W) := by
  obtain ⟨g,hg⟩ := exists_even_permutation_of_weight (by decide : 3 ≤ Fintype.card (Fin 6))
    (pair+sixCoreConstant).val w.val (by simpa only [hw] using
      (show wordWeight (pair+sixCoreConstant).val = 4 by decide))
  have hg' : rho g (pair+sixCoreConstant) = w := Subtype.ext hg
  have hm : (moved pair).map (rho g) = moved w := by
    have hh := moved_conjugate g (pair+sixCoreConstant)
    rw [hg'] at hh
    simpa only [moved,four_residual] using hh
  refine ⟨?_,?_,?_⟩
  · rw [←hm,←Nat.card_congr
      (Submodule.equivMapOfInjective (rho g) (rho.apply_bijective g).injective
        (moved pair)).toEquiv]
    exact pair_card
  · intro hc
    rw [←hm] at hc
    obtain ⟨v,hv,hvc⟩ := hc
    have he : v = sixCoreConstant := (rho.apply_bijective g).injective
      (hvc.trans (sixCoreConstant_fixed g).symm)
    exact pair_not_constant (he ▸ hv)
  · have hr : (residual pair).map (MulAut.conj g).toMonoidHom = residual w := by
      have hh := residual_conjugate g (pair+sixCoreConstant)
      simpa only [hg',four_residual] using hh
    have hd := Submodule.map_mono (f := rho g) pair_double_le
    rw [subspaceCommutator_map_conj,hm,
      map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,hr] at hd
    simpa only [Submodule.map_span,Set.image_singleton,hg'] using hd

end BinaryPermutation.SixCoreResidualLine
