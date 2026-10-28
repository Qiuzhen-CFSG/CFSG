module
public import Theory.Representation.BinaryAlternatingSevenControl.PointGeneration
public import Theory.Representation.BinaryConjugationSection

/-!
# A₇ point generation on the original conjugation section

A faithful binary four-space action of A₇ has generating stabilizers at any
two distinct nonzero vectors. Pull those stabilizers back through the supplied
surjective actor. Injective coordinates of the section with trivial kernel
identify these preimages with the original point centralizers inside Y.
The literal centralizers therefore generate Y, including its action kernel.

Source: Aschbacher--Smith, final step of 12.2.19, printed p.802.
-/

public section
open Subgroup Representation.BinaryOffender
namespace Representation.BinaryConjugationSection
open BinaryAlternatingSevenControl
variable {G : Type*} [Group G] {Y J : Subgroup G}
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem point_centralizers_generate_of_alternatingSeven
    (ρ : Representation (ZMod 2) A7 W) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 4)
    (f : Y →* A7) (hs : Function.Surjective f)
    (C : BinaryConjugationSection Y J ⊥ (ρ.comp f))
    (v w : J) (hv : v ≠ 1) (hw : w ≠ 1) (hvw : v ≠ w) :
    (centralizer ({(v : G)} : Set G)).subgroupOf Y ⊔
      (centralizer ({(w : G)} : Set G)).subgroupOf Y = ⊤ := by
  have hi : Function.Injective C.coordinates := by
    apply C.coordinates.ker_eq_bot_iff.mp
    rw [C.kernel_eq, bot_subgroupOf]
  let cv := (C.coordinates v).toAdd
  let cw := (C.coordinates w).toAdd
  have hcv : cv ≠ 0 := by
    intro he
    apply hv
    apply hi
    exact he.trans (map_one C.coordinates).symm
  have hcw : cw ≠ 0 := by
    intro he
    apply hw
    apply hi
    exact he.trans (map_one C.coordinates).symm
  have hcvw : cv ≠ cw := fun he => hvw (hi he)
  have hle (z : J) :
      (subspaceKernel ρ (Submodule.span (ZMod 2) {(C.coordinates z).toAdd}) ⊤).comap f ≤
        (centralizer ({(z : G)} : Set G)).subgroupOf Y := by
    intro y hy
    have hfixed := hy.2 (C.coordinates z).toAdd (Submodule.subset_span (Set.mem_singleton _))
    have he := (C.equivariant y z).trans hfixed
    have hj := hi he
    have hg := congrArg Subtype.val hj
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hg)
  have hgen := distinct_vector_kernels_generate ρ hf hd hcv hcw hcvw
  have hpre := congrArg (Subgroup.comap f) hgen
  rw [← Subgroup.comap_sup_eq f _ _ hs, Subgroup.comap_top] at hpre
  apply top_unique
  rw [← hpre]
  exact sup_le ((hle v).trans le_sup_left) ((hle w).trans le_sup_right)

end Representation.BinaryConjugationSection
