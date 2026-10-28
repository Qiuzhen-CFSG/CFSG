module
public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Enlarged.Parameters
public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Enlarged.Census
/-!
# Exhaustive parameterization of enlarged rotating cubics

The action on the common four-group determines the first four basis images
from one vector. The central basis images lie in its fixed three-space.
Movement of the two literal factors forces the two movement tests of the
finite census; no assumption on the size of a coordinate normalizer is used.
The census then yields one of the three checked representatives.

Source: Aschbacher–Smith, proof of 14.4.4, printed p.1007, with the possible
central plane retained throughout the split-block calculation.
-/
@[expose] public section
namespace BinarySixSplitPair
open Subgroup
private theorem selected_pow (n : ℕ) (a : Fin 64) :
    decode (if n%2=1 then a else 0) = decode a ^ ((n%2 : ℕ) : ZMod 2).val := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp only [h,show (0:ℕ)≠1 from by decide,if_false,Nat.cast_zero,ZMod.val_zero,pow_zero]
    decide +kernel
  · simp only [h,if_true,Nat.cast_one,ZMod.val_one,pow_one]

theorem decode_linear (a : Fin 6 → Fin 64) (x : Fin 64) :
    decode (Census.linear a x) = binaryWord (fun i => decode (a i)) x := by
  simp only [Census.linear,show Census.bx=bx from rfl,decode_bx,selected_pow]
  rfl

theorem permAction_linear (f : MulAut E) :
    (permAction f : Fin 64 → Fin 64) = Census.linear (fun i => labels (f (basisSix i))) := by
  funext x
  apply labels.symm.injective
  change decode (labels (f (decode x))) = decode (Census.linear _ x)
  rw [show decode (labels (f (decode x))) = f (decode x) from labels.symm_apply_apply _]
  rw [decode_linear,automorphism_expansion]
  congr 1
  funext i
  exact (labels.symm_apply_apply _).symm

private theorem labels_r : ∀ x : Fin 64, labels (r (decode x)) = Census.r x := by decide +kernel
private theorem labels_c : ∀ x : Fin 64, labels (c (decode x)) = Census.c x := by decide +kernel

private theorem fixed_parameters : ∀ x : Fin 64, r (decode x)=decode x → c (decode x)=decode x →
    ∃ u : Fin 8, Census.fixed u=x := by decide +kernel

private theorem seed_parameters : ∀ t : Fin 64,
    (r*c) (c (decode t)*decode t) = (c (decode t)*decode t)*point →
    ∃ i : Fin 32, Census.seeds i=t := by decide +kernel

private theorem decode_mem_left : ∀ x : Fin 64, decode x ∈ leftFactor ↔ x.val<16 := by
  change ∀ x : Fin 64, True ∧ (decode x).2 = 1 ↔ x.val<16
  decide +kernel
private theorem decode_mem_right : ∀ x : Fin 64, decode x ∈ rightFactor ↔ x.val%16=0 := by
  change ∀ x : Fin 64, (decode x).1 = 1 ∧ True ↔ x.val%16=0
  decide +kernel

private theorem oriented_parameters (f : MulAut E)
    (hr : f*r*f⁻¹=c) (hc : f*c*f⁻¹=r*c) (hz : f point=point) :
    ∃ t : Fin 32, ∃ u v : Fin 8,
      (permAction f : Fin 64 → Fin 64) = Census.candidate (Census.seeds t) u v := by
  let t := labels (f (basisSix 2))
  have ht : decode t = f (basisSix 2) := labels.symm_apply_apply _
  have hre (v : E) : f (r v)=c (f v) :=
    DFunLike.congr_fun (mul_inv_eq_iff_eq_mul.mp hr) v
  have hce (v : E) : f (c v)=(r*c) (f v) :=
    DFunLike.congr_fun (mul_inv_eq_iff_eq_mul.mp hc) v
  have he := oriented_basis_images f hr hc hz
  have he0 : f (basisSix 0)=c (f (basisSix 2))*f (basisSix 2) := congrFun he 0
  have htcond : (r*c) (c (decode t)*decode t)=(c (decode t)*decode t)*point := by
    rw [ht,←he0,←hce,show c (basisSix 0)=basisSix 0*point from by decide +kernel,map_mul,hz]
  obtain ⟨i,hi⟩ := seed_parameters t htcond
  have fixed (j : Fin 6) (hj : j=4 ∨ j=5) :
      ∃ u : Fin 8, Census.fixed u=labels (f (basisSix j)) := by
    apply fixed_parameters
    rw [show decode (labels (f (basisSix j)))=f (basisSix j) from labels.symm_apply_apply _]
    · have hrf : r (basisSix j)=basisSix j := by rcases hj with rfl | rfl <;> decide +kernel
      have hcf : c (basisSix j)=basisSix j := by rcases hj with rfl | rfl <;> decide +kernel
      have h1 := (hre (basisSix j)).symm.trans (congrArg f hrf)
      have h2 := (hce (basisSix j)).symm.trans (congrArg f hcf)
      change r (c (f (basisSix j)))=f (basisSix j) at h2
      rwa [h1] at h2
    · rw [show decode (labels (f (basisSix j)))=f (basisSix j) from labels.symm_apply_apply _]
      have hrf : r (basisSix j)=basisSix j := by rcases hj with rfl | rfl <;> decide +kernel
      exact (hre (basisSix j)).symm.trans (congrArg f hrf)
  obtain ⟨u,hu⟩ := fixed 4 (Or.inl rfl)
  obtain ⟨v,hv⟩ := fixed 5 (Or.inr rfl)
  refine ⟨i,u,v,?_⟩
  rw [permAction_linear,Census.candidate,hi]
  congr 1
  funext j
  fin_cases j
  · change labels (f (basisSix 0))=Census.bx (Census.c t) t
    rw [he0,labels_mul,←ht,labels_c,show labels (decode t)=t from labels.apply_symm_apply t]
    rfl
  · change labels (f (basisSix 1))=2
    rw [show f (basisSix 1)=point from congrFun he 1,labels_point]
  · rfl
  · change labels (f (basisSix 3))=Census.bx (Census.r (Census.c t)) t
    rw [show f (basisSix 3)=(r*c) (f (basisSix 2))*f (basisSix 2) from congrFun he 3,labels_mul]
    change bx (labels (r (c (f (basisSix 2))))) t = _
    rw [←ht,←labels_c t,←labels_r]
    rw [show decode (labels (c (decode t)))=c (decode t) from labels.symm_apply_apply _]
    rfl
  · exact hu.symm
  · exact hv.symm

private theorem left_exponents : ∀ x : Fin 64, x.val<16 →
    ((decode x).2.toAdd 0).val=0 ∧ ((decode x).2.toAdd 1).val=0 := by decide +kernel
private theorem right_exponents : ∀ x : Fin 64, x.val%16=0 →
    ((decode x).1.toAdd 0).val=0 ∧ ((decode x).1.toAdd 1).val=0 ∧
    ((decode x).1.toAdd 2).val=0 ∧ ((decode x).1.toAdd 3).val=0 := by decide +kernel

private theorem map_left_eq_of_basis (f : MulAut E)
    (hb : ∀ i : Fin 4, f (basisSix ⟨i.val,by omega⟩) ∈ leftFactor) :
    leftFactor.map f.toMonoidHom=leftFactor := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,rfl⟩ := labels.symm.surjective x
    change decode i ∈ leftFactor at hx
    change f (decode i) ∈ leftFactor
    obtain ⟨h4,h5⟩ := left_exponents i ((decode_mem_left i).mp hx)
    rw [automorphism_expansion]
    simp only [binaryWord,h4,h5,pow_zero,mul_one]
    exact leftFactor.mul_mem (leftFactor.mul_mem (leftFactor.mul_mem
      (leftFactor.pow_mem (hb 0) _) (leftFactor.pow_mem (hb 1) _))
        (leftFactor.pow_mem (hb 2) _)) (leftFactor.pow_mem (hb 3) _)
  · rw [card_map_of_injective f.injective]

private theorem map_right_eq_of_basis (f : MulAut E)
    (h4 : f (basisSix 4) ∈ rightFactor) (h5 : f (basisSix 5) ∈ rightFactor) :
    rightFactor.map f.toMonoidHom=rightFactor := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,rfl⟩ := labels.symm.surjective x
    change decode i ∈ rightFactor at hx
    change f (decode i) ∈ rightFactor
    obtain ⟨h0,h1,h2,h3⟩ := right_exponents i ((decode_mem_right i).mp hx)
    rw [automorphism_expansion]
    simp only [binaryWord,h0,h1,h2,h3,pow_zero,one_mul]
    exact rightFactor.mul_mem (rightFactor.pow_mem h4 _) (rightFactor.pow_mem h5 _)
  · rw [card_map_of_injective f.injective]

private theorem oriented_moving_parameters (f : MulAut E)
    (hr : f*r*f⁻¹=c) (hc : f*c*f⁻¹=r*c) (hz : f point=point)
    (hl : leftFactor.map f.toMonoidHom ≠ leftFactor)
    (hd : rightFactor.map f.toMonoidHom ≠ rightFactor)
    (t : Fin 32) (u v : Fin 8)
    (he : (permAction f : Fin 64 → Fin 64)=Census.candidate (Census.seeds t) u v) :
    (Census.seeds t).val ≥ 16 ∧
      ((Census.fixed u).val%16 ≠ 0 ∨ (Census.fixed v).val%16 ≠ 0) := by
  have hb : ∀ t : Fin 64, ∀ u v : Fin 8,
      Census.candidate t u v 4=t ∧ Census.candidate t u v 16=Census.fixed u ∧
      Census.candidate t u v 32=Census.fixed v := by
    intro t u v
    simp [Census.candidate,Census.linear,Census.bx,Fin.ext_iff]
  have h2 : labels (f (basisSix 2))=Census.seeds t :=
    (congrFun he 4).trans (hb _ u v).1
  have h4 : labels (f (basisSix 4))=Census.fixed u :=
    (congrFun he 16).trans (hb _ u v).2.1
  have h5 : labels (f (basisSix 5))=Census.fixed v :=
    (congrFun he 32).trans (hb _ u v).2.2
  constructor
  · by_contra hn
    have ht : f (basisSix 2) ∈ leftFactor := by
      rw [←labels.symm_apply_apply (f (basisSix 2))]
      change decode (labels (f (basisSix 2))) ∈ leftFactor
      rw [decode_mem_left,h2]
      omega
    have hct : c (f (basisSix 2)) ∈ leftFactor := ht
    have hrct : (r*c) (f (basisSix 2)) ∈ leftFactor := ht
    apply hl
    apply map_left_eq_of_basis
    intro i
    have hei := oriented_basis_images f hr hc hz
    fin_cases i
    · change f (basisSix 0) ∈ leftFactor
      rw [show f (basisSix 0)=c (f (basisSix 2))*f (basisSix 2) from congrFun hei 0]
      exact leftFactor.mul_mem hct ht
    · change f (basisSix 1) ∈ leftFactor
      rw [show f (basisSix 1)=point from congrFun hei 1]
      exact ⟨trivial,rfl⟩
    · exact ht
    · change f (basisSix 3) ∈ leftFactor
      rw [show f (basisSix 3)=(r*c) (f (basisSix 2))*f (basisSix 2) from congrFun hei 3]
      exact leftFactor.mul_mem hrct ht
  · by_contra hn
    push Not at hn
    apply hd
    apply map_right_eq_of_basis
    · rw [←labels.symm_apply_apply (f (basisSix 4))]
      change decode (labels (f (basisSix 4))) ∈ rightFactor
      rw [decode_mem_right,h4]
      exact hn.1
    · rw [←labels.symm_apply_apply (f (basisSix 5))]
      change decode (labels (f (basisSix 5))) ∈ rightFactor
      rw [decode_mem_right,h5]
      exact hn.2

theorem oriented_census (f : MulAut E) (hf : RotatingCubic f)
    (hr : f*r*f⁻¹=c) (hc : f*c*f⁻¹=r*c) :
    ∃ j : Fin 3, ∃ k : Fin 24, ∀ x : Fin 64,
      Census.change k (permAction f x) = Census.rep j (Census.change k x) := by
  obtain ⟨t,u,v,he⟩ := oriented_parameters f hr hc hf.2.1
  obtain ⟨hl,hd⟩ := oriented_moving_parameters f hr hc hf.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 t u v he
  have hcube : (permAction f)^3=1 := by rw [←map_pow,hf.1,map_one]
  have hparam := Census.census t u v
  dsimp only at hparam
  have hthree : ∀ i : Fin 6,
      Census.candidate (Census.seeds t) u v
        (Census.candidate (Census.seeds t) u v
          (Census.candidate (Census.seeds t) u v (![1,2,4,8,16,32] i))) =
            ![1,2,4,8,16,32] i := by
    rw [←he]
    intro i
    exact Equiv.congr_fun hcube _
  obtain ⟨j,k,hk⟩ := hparam hthree hl (by
    rcases hd with hu | hv
    · exact Or.inl (fun h => hu (congrArg Fin.val h))
    · exact Or.inr (fun h => hv (congrArg Fin.val h)))
  exact ⟨j,k,fun x => by rw [he]; exact hk x⟩

end BinarySixSplitPair
