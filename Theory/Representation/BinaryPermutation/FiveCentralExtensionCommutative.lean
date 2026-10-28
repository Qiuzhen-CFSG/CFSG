module

public import Theory.Representation.BinaryPermutation.FiveAlternatingBilinear
public import Theory.GroupTheory.Commutator.CentralExtensionPairing
public import Mathlib.Algebra.Module.ZMod

/-!
# A central extension of two marked five-point cores is commutative

The kernel and quotient carry the same literal binary deleted-permutation
action. Their common actor may be any group mapping onto A₅; an A₅ action
on the whole extension is not assumed. The actual commutators descend to
an alternating bilinear map from the quotient to the kernel. Equivariance
for the supplied actor descends along its surjection to A₅, so the finite
five-point vanishing theorem kills every commutator in the original group.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace BinaryPermutation.FiveCentralExtension
private abbrev C := core (Fin 5)
private abbrev act (a : alternatingGroup (Fin 5)) := coreRepresentation (Fin 5) a.val
variable {D L : Type*} [Group D] [Group L]

/-- A central extension whose kernel and quotient have actual equivariant
five-point-core markings is commutative. The actor on the extension need
only surject onto A₅. -/
theorem isMulCommutative_of_marked_kernel_and_quotient
    (q : D →* Multiplicative (core (Fin 5))) (hq : Function.Surjective q)
    (i : Multiplicative (core (Fin 5)) →* D) (hi : Function.Injective i)
    (hir : i.range = q.ker) (hcentral : q.ker ≤ center D)
    (ρ : L →* MulAut D) (π : L →* alternatingGroup (Fin 5))
    (hπ : Function.Surjective π)
    (hquot : ∀ l x, q (ρ l x) = Multiplicative.ofAdd
      (coreRepresentation (Fin 5) (π l).val (q x).toAdd))
    (hker : ∀ l v, ρ l (i v) = i (Multiplicative.ofAdd
      (coreRepresentation (Fin 5) (π l).val v.toAdd))) : IsMulCommutative D := by
  obtain ⟨B,hB⟩ := CentralExtension.exists_lift_commutator_pairing q hq hcentral
    (MonoidHom.id (Multiplicative C))
  have hmem (x y : C) : ((B x y).toMul : D) ∈ q.ker := by
    obtain ⟨a,ha⟩ := hq (Multiplicative.ofAdd x)
    obtain ⟨b,hb⟩ := hq (Multiplicative.ofAdd y)
    rw [hB x y a b ha hb,MonoidHom.mem_ker,map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  let e : Multiplicative C ≃* q.ker :=
    (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hir)
  have he (z : q.ker) : i (e.symm z) = (z : D) :=
    congrArg Subtype.val (e.apply_symm_apply z)
  let f (x y : C) : C := (e.symm ⟨(B x y).toMul,hmem x y⟩).toAdd
  have hf (x y : C) : i (Multiplicative.ofAdd (f x y)) = ((B x y).toMul : D) :=
    he ⟨(B x y).toMul,hmem x y⟩
  have hf0 (x : C) : f x 0 = 0 := by
    apply Multiplicative.ofAdd.injective
    apply hi
    rw [hf,map_zero]
    exact (map_one i).symm
  have h0f (y : C) : f 0 y = 0 := by
    apply Multiplicative.ofAdd.injective
    apply hi
    rw [hf,map_zero]
    exact (map_one i).symm
  have hfadd (x y z : C) : f x (y+z) = f x y + f x z := by
    apply Multiplicative.ofAdd.injective
    apply hi
    change i (Multiplicative.ofAdd (f x (y+z))) =
      i (Multiplicative.ofAdd (f x y) * Multiplicative.ofAdd (f x z))
    rw [map_mul,hf,hf,hf]
    exact congrArg (fun w : Additive (center D) => (w.toMul : D)) (map_add (B x) y z)
  have haddf (x y z : C) : f (x+y) z = f x z + f y z := by
    apply Multiplicative.ofAdd.injective
    apply hi
    change i (Multiplicative.ofAdd (f (x+y) z)) =
      i (Multiplicative.ofAdd (f x z) * Multiplicative.ofAdd (f y z))
    rw [map_mul,hf,hf,hf]
    exact congrArg (fun w : Additive (center D) => (w.toMul : D))
      (DFunLike.congr_fun (map_add B x y) z)
  let F : C →+ C →+ C := {
    toFun x := { toFun := f x, map_zero' := hf0 x, map_add' := hfadd x }
    map_zero' := AddMonoidHom.ext h0f
    map_add' x y := AddMonoidHom.ext (haddf x y) }
  let b : C →ₗ[ZMod 2] C →ₗ[ZMod 2] C :=
    ((AddMonoidHom.toZModLinearMapEquiv 2).toAddMonoidHom.comp F).toZModLinearMap 2
  have hb (x y : C) (a d : D)
      (ha : q a = Multiplicative.ofAdd x) (hd : q d = Multiplicative.ofAdd y) :
      i (Multiplicative.ofAdd (b x y)) = ⁅a,d⁆ :=
    (hf x y).trans (hB x y a d ha hd)
  have halt (x : C) : b x x = 0 := by
    obtain ⟨a,ha⟩ := hq (Multiplicative.ofAdd x)
    apply Multiplicative.ofAdd.injective
    apply hi
    rw [hb x x a a ha ha,commutatorElement_self]
    exact (map_one i).symm
  have heq (a : alternatingGroup (Fin 5)) (x y : C) :
      b (act a x) (act a y) = act a (b x y) := by
    obtain ⟨l,hl⟩ := hπ a
    obtain ⟨u,hu⟩ := hq (Multiplicative.ofAdd x)
    obtain ⟨v,hv⟩ := hq (Multiplicative.ofAdd y)
    have hlu : q (ρ l u) = Multiplicative.ofAdd (act a x) := by
      simpa only [hu,hl,toAdd_ofAdd,act] using hquot l u
    have hlv : q (ρ l v) = Multiplicative.ofAdd (act a y) := by
      simpa only [hv,hl,toAdd_ofAdd,act] using hquot l v
    apply Multiplicative.ofAdd.injective
    apply hi
    calc
      i (Multiplicative.ofAdd (b (act a x) (act a y))) = ⁅ρ l u,ρ l v⁆ :=
        hb _ _ _ _ hlu hlv
      _ = ρ l ⁅u,v⁆ := (map_commutatorElement (ρ l) u v).symm
      _ = ρ l (i (Multiplicative.ofAdd (b x y))) := by rw [hb x y u v hu hv]
      _ = i (Multiplicative.ofAdd (act a (b x y))) := by
        simpa only [hl,toAdd_ofAdd,act] using hker l (Multiplicative.ofAdd (b x y))
  have hz : b = 0 := FiveAlternatingBilinear.eq_zero b halt heq
  refine ⟨⟨fun x y => commutatorElement_eq_one_iff_mul_comm.mp ?_⟩⟩
  have hh := hb (q x).toAdd (q y).toAdd x y rfl rfl
  rw [hz,LinearMap.zero_apply,LinearMap.zero_apply] at hh
  exact hh.symm.trans (map_one i)

end BinaryPermutation.FiveCentralExtension
