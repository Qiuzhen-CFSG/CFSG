module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index

/-!
# Automorphisms over a characteristic subgroup of index two

If a finite group `G` has a characteristic subgroup `C` of index two, and
both `C` and its automorphism group are two-groups, then `MulAut G` is a
two-group. This is a general prerequisite for the local automorphism
analysis underlying Alperin--Brauer--Gorenstein, Chapter II, Section 1,
Proposition 1 (article pp. 10--11); that proposition states the
quasi-dihedral fusion alternatives without giving this intermediate proof.

Restrict automorphisms to `C`. For an element `b` outside `C`, the kernel
embeds in `C` by sending `f` to `b⁻¹ * f b`: the index-two condition puts
this displacement in `C`, and pointwise fixation of `C` makes it a
homomorphism. Agreement on `C` and `b` implies agreement everywhere.
The kernel and restriction image are therefore two-groups, so the
extension is a two-group. Neither commutativity nor a splitting of `G`
over `C` is required. All intermediate constructions remain private.
-/

namespace Subgroup

variable {G : Type*} [Group G] (C : Subgroup G) [C.Characteristic]

private lemma characteristic_mem_iff (f : MulAut G) (x : G) :
    f x ∈ C ↔ x ∈ C := by
  change x ∈ C.comap f.toMonoidHom ↔ x ∈ C
  rw [characteristic_iff_comap_eq.mp inferInstance f]

private lemma kernel_fixes (f : (MulAut.characteristic C).ker) (x : G) (hx : x ∈ C) :
    (f : MulAut G) x = x := by
  have h := DFunLike.congr_fun f.property (⟨x, hx⟩ : C)
  exact congrArg Subtype.val h

private def kernelDisplacement (hi : C.index = 2) (b : G) :
    (MulAut.characteristic C).ker →* C where
  toFun f := ⟨b⁻¹ * (f : MulAut G) b, by
    rw [C.mul_mem_iff_of_index_two hi]
    simp only [C.inv_mem_iff, characteristic_mem_iff]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' f g := by
    apply Subtype.ext
    change b⁻¹ * (f : MulAut G) ((g : MulAut G) b) =
      (b⁻¹ * (f : MulAut G) b) * (b⁻¹ * (g : MulAut G) b)
    have hd : b⁻¹ * (g : MulAut G) b ∈ C := by
      rw [C.mul_mem_iff_of_index_two hi]
      simp only [C.inv_mem_iff, characteristic_mem_iff]
    have hf := kernel_fixes C f _ hd
    rw [map_mul, map_inv] at hf
    calc
      _ = b⁻¹ * ((f : MulAut G) b *
        ((f : MulAut G) b)⁻¹ * (f : MulAut G) ((g : MulAut G) b)) := by simp
      _ = _ := by rw [mul_assoc ((f : MulAut G) b), hf, mul_assoc]

private lemma kernelDisplacement_injective (hi : C.index = 2) (b : G) (hb : b ∉ C) :
    Function.Injective (kernelDisplacement C hi b) := by
  intro f g h
  have hval := congrArg Subtype.val h
  change b⁻¹ * (f : MulAut G) b = b⁻¹ * (g : MulAut G) b at hval
  have hbeq := mul_left_cancel hval
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  by_cases hx : x ∈ C
  · rw [kernel_fixes C f x hx, kernel_fixes C g x hx]
  · have hd : b⁻¹ * x ∈ C := by
      rw [C.mul_mem_iff_of_index_two hi]
      simp [hb, hx]
    have hf := kernel_fixes C f _ hd
    have hg := kernel_fixes C g _ hd
    rw [map_mul, map_inv] at hf hg
    rw [hbeq] at hf
    exact mul_left_cancel (hf.trans hg.symm)

/-- A finite group's automorphism group is a two-group if it has a characteristic
subgroup of index two which, together with its automorphism group, is a two-group. -/
public theorem isPGroup_mulAut_of_characteristic_index_two [Finite G]
    (hi : C.index = 2) (hC : IsPGroup 2 C) (hA : IsPGroup 2 (MulAut C)) :
    IsPGroup 2 (MulAut G) := by
  obtain ⟨b, hb, _⟩ := C.index_eq_two_iff_exists_notMem_and.mp hi
  have hk : IsPGroup 2 (MulAut.characteristic C).ker :=
    hC.of_injective (kernelDisplacement C hi b) (kernelDisplacement_injective C hi b hb)
  have ht := (hA.to_subgroup ⊤).comap_of_ker_isPGroup (MulAut.characteristic C) hk
  rw [Subgroup.comap_top] at ht
  exact ht.of_surjective (⊤ : Subgroup (MulAut G)).subtype (by
    intro f
    exact ⟨⟨f, mem_top f⟩, rfl⟩)

end Subgroup
