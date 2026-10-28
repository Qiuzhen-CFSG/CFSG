module

public import Theory.GroupTheory.Commutator.CentralSylowTransfer
public import Theory.GroupTheory.Commutator.CentralDihedral

/-!
# Two-primary central kernels and dihedral Sylow images

For a finite central extension with two-group kernel, the derived part of
the kernel has order at most two whenever its actual quotient Sylow image
is dihedral. The central kernel lies in every Sylow two-subgroup. Transfer
puts its ambient derived part in the Sylow derived subgroup, giving an
injection into the central derived part of the Sylow subgroup. Restricting
the original surjection to its exact image makes that subgroup a central
dihedral cover, where the bound is already proved.

This is the two-primary kernel calculation for the Schur-cover step in
Alperin--Brauer--Gorenstein, Chapter II, Section 3, Proposition 2. It does not
assume perfectness, kernel cyclicity, or a full Schur-multiplier formula.
-/

namespace CentralExtension
open Subgroup

/-- A central two-kernel has at most two derived elements if the actual image
of a Sylow two-subgroup is dihedral. -/
public theorem card_ker_inf_commutator_le_two_of_dihedral_sylow
    {E B : Type*} [Group E] [Finite E] [Group B] [Finite B]
    (f : E →* B) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center E) (hkernel : IsPGroup 2 f.ker)
    (S : Sylow 2 E) {n : ℕ} [NeZero n]
    (e : Sylow.mapSurjective hf S ≃* DihedralGroup n) :
    Nat.card (f.ker ⊓ _root_.commutator E : Subgroup E) ≤ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Sylow 2 B := Sylow.mapSurjective hf S
  let q : S →* T := f.subgroupMap (S : Subgroup E)
  have hq : Function.Surjective q := f.subgroupMap_surjective (S : Subgroup E)
  let g : S →* DihedralGroup n := e.toMonoidHom.comp q
  have hg : Function.Surjective g := e.surjective.comp hq
  have hgcenter : g.ker ≤ center S := by
    intro x hx
    have hqx : q x = 1 := by
      apply e.injective
      change e (q x) = 1 at hx
      exact hx.trans e.map_one.symm
    have hxker : (x : E) ∈ f.ker := by
      exact congrArg Subtype.val hqx
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact mem_center_iff.mp (hcentral hxker) (y : E)
  have hbound := card_center_inf_commutator_le_two_of_dihedral g hg hgcenter
  let A : Subgroup E := f.ker ⊓ _root_.commutator E
  let C : Subgroup S := center S ⊓ _root_.commutator S
  have hkerS : f.ker ≤ (S : Subgroup E) := hkernel.le_sylow_of_normal S
  have hA (x : A) : (⟨(x : E), hkerS x.property.1⟩ : S) ∈ C := by
    rcases x with ⟨x, hxker, hxderived⟩
    change (⟨x, hkerS hxker⟩ : S) ∈ center S ⊓ _root_.commutator S
    constructor
    · apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact mem_center_iff.mp (hcentral hxker) (y : E)
    · have hder : x ∈ ⁅(S : Subgroup E), (S : Subgroup E)⁆ :=
        center_inf_commutator_inf_sylow_le_commutator S
          ⟨⟨hcentral hxker, hxderived⟩, hkerS hxker⟩
      rw [← map_subtype_commutator] at hder
      obtain ⟨y, hy, hxy⟩ := hder
      have heq : y = ⟨x, hkerS hxker⟩ := Subtype.ext hxy
      simpa [heq] using hy
  let i : A → C := fun x => ⟨⟨(x : E), hkerS x.property.1⟩, hA x⟩
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : C => ((z : S) : E)) hxy
  exact (Nat.card_le_card_of_injective i hi).trans hbound

end CentralExtension
