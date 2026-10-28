module
public import Theory.Representation.BinaryAlternatingNaturalCohomology.SixTransitive
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreGeometry
public import Mathlib.RepresentationTheory.Intertwining
public import Theory.Representation.BinaryOffender.PermutationConjugacy
/-!
# Fixed vectors of the binary S6 point core in a natural extension

Let a binary S6-module contain the marked natural four-dimensional module,
and suppose all A6 displacements lie in that submodule. A point-core fixed
vector then lies in the sum of the natural submodule and the A6 fixed space.
The proof associates its displacement cocycle on A6. Every such cocycle comes
from a full permutation vector. The point-core double transposition and odd
swap force that vector to have augmentation zero, so the cocycle is principal.
The conjugate form retains the specified conjugating element.

This is a fixed-vector statement for the actual extension; it requires no
fixed complement in the whole module. Source application: Meierfrankenfeld--
Stellmacher (1993), (5.3), printed p.915, in the full point-core branch.
-/

@[expose] public section
open Subgroup BinaryPermutation Representation Representation.OneCohomology
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace BinaryPermutation.PointCoreFixed
abbrev a : S := swap01 * swap23
private theorem ha : a ∈ alternatingGroup (Fin 6) := by decide
private def conjAlt (t : S) (g : alternatingGroup (Fin 6)) : alternatingGroup (Fin 6) :=
 ⟨t*g.val*t⁻¹, (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ g.property t⟩
private theorem displacement_conj (t : S) (w : Full (Fin 6))
 (g : alternatingGroup (Fin 6)) :
 (naturalDisplacement (Fin 6) (representation (Fin 6) t w)).val (conjAlt t g) =
 naturalRepresentation (Fin 6) t ((naturalDisplacement (Fin 6) w).val g) := by
 apply Subtype.ext
 change (constants (Fin 6)).mkQ
  (representation (Fin 6) (t*g.val*t⁻¹) (representation (Fin 6) t w) - representation (Fin 6) t w) =
 deletedRepresentation (Fin 6) t ((constants (Fin 6)).mkQ (representation (Fin 6) g.val w-w))
 rw [deletedRepresentation_mk]
 congr 1
 rw [map_sub]
 rw [map_mul, map_mul]
 change representation (Fin 6) t (representation (Fin 6) g.val
  (representation (Fin 6) t⁻¹ (representation (Fin 6) t w))) - _ = _
 have he : representation (Fin 6) t⁻¹ (representation (Fin 6) t w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
 rw [he]

private theorem full_fixed_of_displacement_zero (w : Full (Fin 6))
 (g : alternatingGroup (Fin 6)) (h4 : g.val 4 = 4)
 (h : (naturalDisplacement (Fin 6) w).val g = 0) :
 representation (Fin 6) g.val w = w := by
 have hc : representation (Fin 6) g.val w-w ∈ constants (Fin 6) := by
  apply (Submodule.Quotient.mk_eq_zero _).mp
  exact congrArg (fun v : natural (Fin 6) => (v : Deleted (Fin 6))) h
 obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hc
 have he := congrFun hc 4
 have hi : g.val.symm 4=4 := (Equiv.symm_apply_eq _).mpr h4.symm
 have hz : c=0 := by simpa [allOne,representation_apply,hi] using he
 rw [hz,zero_smul] at hc
 exact sub_eq_zero.mp hc.symm

private theorem augmentation_zero (w : Full (Fin 6))
 (ha0 : (naturalDisplacement (Fin 6) w).val ⟨a,ha⟩=0)
 (hc : ∀g : alternatingGroup (Fin 6),
  (naturalDisplacement (Fin 6) w).val (conjAlt swap45 g) =
  naturalRepresentation (Fin 6) swap45 ((naturalDisplacement (Fin 6) w).val g)) :
 augmentation (Fin 6) w = 0 := by
 have hD : naturalDisplacement (Fin 6) (representation (Fin 6) swap45 w) =
  naturalDisplacement (Fin 6) w := by
  apply Subtype.ext
  funext g
  let g' := conjAlt swap45 g
  have he : conjAlt swap45 g'=g := by
   apply Subtype.ext
   change swap45*(swap45*g.val*swap45⁻¹)*swap45⁻¹=g.val
   have ht : swap45*swap45=1 := by decide
   have hi : swap45⁻¹=swap45 := by decide
   simp only [hi]
   calc
    swap45 * (swap45 * g.val * swap45) * swap45 =
      (swap45*swap45)*g.val*(swap45*swap45) := by group
    _ = g.val := by rw [ht,one_mul,mul_one]
  calc
   (naturalDisplacement (Fin 6) (representation (Fin 6) swap45 w)).val g =
     (naturalDisplacement (Fin 6) (representation (Fin 6) swap45 w)).val (conjAlt swap45 g') := congrArg _ he.symm
   _ = naturalRepresentation (Fin 6) swap45 ((naturalDisplacement (Fin 6) w).val g') := displacement_conj _ _ _
   _ = (naturalDisplacement (Fin 6) w).val (conjAlt swap45 g') := (hc g').symm
   _ = (naturalDisplacement (Fin 6) w).val g := congrArg _ he
 have hz : naturalDisplacement (Fin 6) (representation (Fin 6) swap45 w-w)=0 := by
  rw [map_sub,hD,sub_self]
 obtain ⟨c,he⟩ := Submodule.mem_span_singleton.mp
  ((naturalDisplacement_eq_zero_iff (Fin 6) (by simp) _).mp hz)
 have hc0 : c=0 := by
  have h := congrFun he 0
  simpa [allOne,representation_apply,swap45,Equiv.swap_apply_def] using h
 have htfix : representation (Fin 6) swap45 w=w := by
  rw [hc0,zero_smul] at he
  exact sub_eq_zero.mp he.symm
 have hafix := full_fixed_of_displacement_zero w ⟨a,ha⟩ (by decide) ha0
 have h01 : w 0=w 1 := by simpa [representation_apply,a,swap01,swap23,Equiv.swap_apply_def] using (congrFun hafix 0).symm
 have h23 : w 2=w 3 := by simpa [representation_apply,a,swap01,swap23,Equiv.swap_apply_def] using (congrFun hafix 2).symm
 have h45 : w 4=w 5 := by simpa [representation_apply,swap45,Equiv.swap_apply_def] using (congrFun htfix 4).symm
 simp only [augmentation,Fin.sum_univ_succ] 
 change w 0+(w 1+(w 2+(w 3+(w 4+(w 5+0)))))=0
 rw [h01,h23,h45]
 calc
  _ = (w 1+w 1)+((w 3+w 3)+(w 5+w 5)) := by abel
  _ = 0 := by simp only [CharTwo.add_self_eq_zero]

variable {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
theorem fixed_le_natural_sup_alternating
 (σ : Representation (ZMod 2) S Y)
 (i : (naturalRepresentation (Fin 6)).IntertwiningMap σ)
 (hi : Function.Injective i)
 (hm : ∀ (g : alternatingGroup (Fin 6)) (x : Y),
   ∃u : natural (Fin 6), i u=σ g.val x-x) :
 Representation.BinaryOffender.fixedSpace σ pointCore ≤
 i.toLinearMap.range ⊔ Representation.BinaryOffender.fixedSpace σ (alternatingGroup (Fin 6)) := by
 classical
 intro x hx
 let v : alternatingGroup (Fin 6) → natural (Fin 6) := fun g => Classical.choose (hm g x)
 have hv (g : alternatingGroup (Fin 6)) : i (v g)=σ g.val x-x := Classical.choose_spec (hm g x)
 let f : cocycles (alternatingNaturalRepresentation (Fin 6)) := ⟨v,by
   intro g h
   apply hi
   rw [map_add]
   change i (v (g*h))=i (naturalRepresentation (Fin 6) g.val (v h))+i (v g)
   rw [hv,i.isIntertwining,hv,hv,map_sub]
   change σ (g.val*h.val) x-x=_
   rw [map_mul,Module.End.mul_apply]
   abel⟩
 have hf (g : alternatingGroup (Fin 6)) : i (f.val g)=σ g.val x-x := hv g
 have hat : a∈pointCore := by
  rw [pointCore_eq_closure]
  exact subset_closure (by simp)
 have htt : swap45∈pointCore := by
  rw [pointCore_eq_closure]
  exact subset_closure (by simp)
 have ht : σ swap45 x=x := hx ⟨swap45,htt⟩
 have hti : σ swap45⁻¹ x=x := by
  have h := congrArg (fun y => σ swap45⁻¹ y) ht
  rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply] at h
  exact h.symm
 have hfa : f.val ⟨a,ha⟩=0 := by
  apply hi
  rw [hf,map_zero]
  have hax : σ a x = x := hx ⟨a,hat⟩
  change σ a x - x = 0
  rw [hax,sub_self]
 have hcov (g : alternatingGroup (Fin 6)) : f.val (conjAlt swap45 g)=
   naturalRepresentation (Fin 6) swap45 (f.val g) := by
  apply hi
  rw [hf,i.isIntertwining,hf,map_sub]
  change σ (swap45*g.val*swap45⁻¹) x-x=σ swap45 (σ g.val x)-σ swap45 x
  rw [map_mul,map_mul]
  change σ swap45 (σ g.val (σ swap45⁻¹ x))-x=_
  rw [hti,ht]
 obtain ⟨w,hw⟩ := alternatingSix_naturalDisplacement_surjective f
 have hw0 : augmentation (Fin 6) w=0 := augmentation_zero w
   (by rw [hw];exact hfa) (by intro g;rw [hw];exact hcov g)
 obtain ⟨u,hu⟩ := (naturalDisplacement_principal_iff (Fin 6) (by simp) (by decide) w).mpr hw0
 have hp (g : alternatingGroup (Fin 6)) :
   i (naturalRepresentation (Fin 6) g.val u-u)=σ g.val x-x := by
  have h := congrArg (fun c : cocycles (alternatingNaturalRepresentation (Fin 6)) => i (c.val g)) (hu.trans hw)
  exact h.trans (hf g)
 have hc : x-i u ∈ Representation.BinaryOffender.fixedSpace σ (alternatingGroup (Fin 6)) := by
  intro g
  change σ g.val (x-i u)=x-i u
  rw [map_sub,← i.isIntertwining]
  have hh := hp g
  rw [map_sub] at hh
  exact sub_eq_sub_iff_sub_eq_sub.mp hh.symm
 apply Submodule.mem_sup.mpr
 exact ⟨i u,⟨u,rfl⟩,x-i u,hc,by abel⟩
theorem fixed_conjugate_le_natural_sup_alternating
 (σ : Representation (ZMod 2) S Y)
 (i : (naturalRepresentation (Fin 6)).IntertwiningMap σ)
 (hi : Function.Injective i)
 (hm : ∀ (g : alternatingGroup (Fin 6)) (x : Y),
   ∃u : natural (Fin 6), i u=σ g.val x-x) (t : S) :
 Representation.BinaryOffender.fixedSpace σ (pointCore.map (MulAut.conj t).toMonoidHom) ≤
 i.toLinearMap.range ⊔ Representation.BinaryOffender.fixedSpace σ (alternatingGroup (Fin 6)) := by
 classical
 intro x hx
 let v := σ t⁻¹ x
 have hv0 : v ∈ Representation.BinaryOffender.fixedSpace σ pointCore := by
  intro a
  have ha : t*a.val*t⁻¹ ∈ pointCore.map (MulAut.conj t).toMonoidHom :=
   ⟨a.val,a.property,rfl⟩
  have hh := congrArg (σ t⁻¹) (hx ⟨_,ha⟩)
  change σ t⁻¹ (σ (t*a.val*t⁻¹) x) = σ t⁻¹ x at hh
  change σ a.val (σ t⁻¹ x) = σ t⁻¹ x
  have hi (z : Y) : σ t⁻¹ (σ t z) = z := by
   rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  simpa only [map_mul,Module.End.mul_apply,hi] using hh
 have hv := fixed_le_natural_sup_alternating σ i hi hm hv0
 obtain ⟨u,⟨w,rfl⟩,y,hy,he⟩ := Submodule.mem_sup.mp hv
 have hte : σ t v = x := by
  change σ t (σ t⁻¹ x) = x
  rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
 have hfix : σ t y ∈ Representation.BinaryOffender.fixedSpace σ (alternatingGroup (Fin 6)) := by
  intro g
  have hg : t⁻¹*g.val*t ∈ alternatingGroup (Fin 6) := by
   simpa only [inv_inv] using (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ g.property t⁻¹
  have hh := hy ⟨_,hg⟩
  change σ g.val (σ t y) = σ t y
  calc
   _ = σ t (σ (t⁻¹*g.val*t) y) := by
    simp only [map_mul,Module.End.mul_apply]
    have htinv (z : Y) : σ t (σ t⁻¹ z) = z := by
     rw [← Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
    rw [htinv]
   _ = σ t y := congrArg (σ t) hh
 apply Submodule.mem_sup.mpr
 refine ⟨i (naturalRepresentation (Fin 6) t w),⟨_,rfl⟩,σ t y,hfix,?_⟩
 rw [i.isIntertwining,←map_add]
 change σ t (i.toLinearMap w+y)=x
 rw [he,hte]
end BinaryPermutation.PointCoreFixed
