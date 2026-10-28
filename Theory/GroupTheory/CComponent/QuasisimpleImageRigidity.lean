module

public import Theory.GroupTheory.CComponent.Radical
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement

/-!
# Rigidity of a supplement in a C-component

Suppose B ≤ D, D is a finite C-component, and D/O₂(D) is quasisimple.
If B and D have the same nontrivial image under a homomorphism, its
kernel inside D is proper and hence solvable. Thus B supplements the
solvable radical of D. When O₂(D) normalizes B, quasisimple supplement
rigidity forces B = D.

The Chapter 13 application compares literal plus images before restricting
the resulting C-component to KLᵥ. Source: the component localization used
in Aschbacher–Smith 13.6.20, p.931, via 1.2.4 and A.3.6.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory

/-- Equal nontrivial images and two-core normalization force equality. -/
theorem IsCComponent.eq_of_image_eq_of_twoCore_normalizes {H X : Type*} [Group H] [Finite H] [Group X]
    (f : H →* X) {B D : Subgroup H} (hD : D.IsCComponent) (hBD : B ≤ D)
    [IsQuasisimple (D ⧸ pCore 2 D)]
    (himage : B.map f = D.map f) (hne : D.map f ≠ ⊥)
    (hnorm : pCore 2 D ≤ normalizer (B.subgroupOf D : Set D)) : B = D := by
  let g := f.subgroupMap D
  have hg : g.ker ≠ ⊤ := by
    intro ht
    apply hne
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro d hd
    have h := ht ▸ (mem_top (⟨d, hd⟩ : D))
    exact congrArg Subtype.val (show g ⟨d, hd⟩ = 1 from h)
  let : Group.IsSolvable g.ker :=
    hD.isSolvable_of_subnormal_lt_top (inferInstance : g.ker.Normal).isSubnormal hg
  have hcover : B.subgroupOf D ⊔ g.ker = ⊤ := by
    apply top_unique
    intro d _
    obtain ⟨b, hb, he⟩ := (himage.symm ▸ (mem_map_of_mem f d.property))
    apply mem_sup_of_normal_right.mpr
    refine ⟨⟨b, hBD hb⟩, hb, ⟨b⁻¹ * d, D.mul_mem (D.inv_mem (hBD hb)) d.property⟩, ?_, ?_⟩
    · apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      change f (b⁻¹ * d) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    · apply Subtype.ext
      simp
  have hrad : solvableRadical D ⊔ B.subgroupOf D = ⊤ := by
    apply top_unique
    rw [← hcover]
    exact sup_le le_sup_right ((le_solvableRadical g.ker inferInstance inferInstance).trans le_sup_left)
  let := hD.perfect
  have hb := eq_top_of_radical_supplement_of_quasisimple_quotient
    (pCore 2 D) (B.subgroupOf D) hnorm hrad
  have he := congrArg (map D.subtype) hb
  simpa only [map_subgroupOf_eq_of_le hBD, ← MonoidHom.range_eq_map, range_subtype] using he

end Theory.GroupTheory
