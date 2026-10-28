module
public import Theory.Representation.BinaryConjugationSection
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Joining two binary conjugation sections with a common kernel

Multiplication maps the two commuting numerators onto their literal join.
The two coordinate maps descend through this multiplication map because the
intersection lies in their common kernel. The descended product coordinates
retain the original action and identify each original numerator by vanishing
of the opposite coordinate. The central kernel is retained throughout.

Source application: Aschbacher--Smith, 14.6.22--24, printed pp.1038--1041,
joining the natural and dual supports on the same component.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  {H A B Z : Subgroup G} {ρ : Representation (ZMod 2) H V}
  {σ : Representation (ZMod 2) H W}

/-- The actual join of two commuting sections with common kernel has product
coordinates. The coordinates retain the original markings on both factors. -/
theorem exists_join_section
    (a : BinaryConjugationSection H A Z ρ)
    (b : BinaryConjugationSection H B Z σ)
    (hc : A ≤ centralizer (B : Set G)) (hi : A ⊓ B ≤ Z) :
    ∃ d : BinaryConjugationSection H (A ⊔ B) Z (ρ.prod σ),
      (∀ x : A, ∀ y : B, d.coordinates ⟨(x:G)*(y:G),mul_mem_sup x.property y.property⟩ =
        Multiplicative.ofAdd ((a.coordinates x).toAdd,(b.coordinates y).toAdd)) ∧
      (∀ x : (A ⊔ B : Subgroup G), (x:G) ∈ A ↔ (d.coordinates x).toAdd.2 = 0) ∧
      (∀ x : (A ⊔ B : Subgroup G), (x:G) ∈ B ↔ (d.coordinates x).toAdd.1 = 0) := by
  have hcomm : ∀ x : A, ∀ y : B, Commute (x:G) (y:G) :=
    fun x y => (hc x.property y y.property).symm
  let m : A × B →* G := A.subtype.noncommCoprod B.subtype hcomm
  have hm : m.range = A ⊔ B := by
    exact (MonoidHom.noncommCoprod_range A.subtype B.subtype hcomm).trans
      (by rw [range_subtype,range_subtype])
  let p : A × B →* (A ⊔ B : Subgroup G) :=
    m.codRestrict _ (fun x => hm ▸ ⟨x,rfl⟩)
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨y,hy⟩ := (show (x:G) ∈ m.range from hm.symm ▸ x.property)
    exact ⟨y,Subtype.ext hy⟩
  let q : A × B →* Multiplicative (V × W) := {
    toFun x := Multiplicative.ofAdd ((a.coordinates x.1).toAdd,(b.coordinates x.2).toAdd)
    map_one' := by simp
    map_mul' x y := by
      change Multiplicative.ofAdd ((a.coordinates (x.1*y.1)).toAdd,
        (b.coordinates (x.2*y.2)).toAdd) = _
      rw [a.coordinates.map_mul,b.coordinates.map_mul]
      rfl }
  have hker : p.ker ≤ q.ker := by
    rintro ⟨x,y⟩ hh
    have hxy : (x:G)*(y:G) = 1 := congrArg Subtype.val hh
    have hxB : (x:G) ∈ B := by
      rw [eq_inv_of_mul_eq_one_left hxy]
      exact B.inv_mem y.property
    have hyA : (y:G) ∈ A := by
      rw [eq_inv_of_mul_eq_one_right hxy]
      exact A.inv_mem x.property
    change Multiplicative.ofAdd _ = 1
    rw [(a.coordinates_eq_one_iff x).mpr (hi ⟨x.property,hxB⟩),
      (b.coordinates_eq_one_iff y).mpr (hi ⟨hyA,y.property⟩)]
    rfl
  let f : (A ⊔ B : Subgroup G) →* Multiplicative (V × W) :=
    p.liftOfSurjective hp ⟨q,hker⟩
  have hf (x : A) (y : B) : f (p (x,y)) = q (x,y) :=
    p.liftOfRightInverse_comp_apply _ _ _ _
  have hnorm : H ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp (a.normalized hg),
      mem_normalizer_iff_map_conj_eq.mp (b.normalized hg)]
  let d : BinaryConjugationSection H (A ⊔ B) Z (ρ.prod σ) := {
    section_le := sup_le a.section_le b.section_le
    kernel_le := a.kernel_le.trans le_sup_left
    normalized := hnorm
    coordinates := f
    onto := by
      intro v
      obtain ⟨x,hx⟩ := a.onto (Multiplicative.ofAdd v.toAdd.1)
      obtain ⟨y,hy⟩ := b.onto (Multiplicative.ofAdd v.toAdd.2)
      refine ⟨p (x,y),?_⟩
      rw [hf]
      change Multiplicative.ofAdd ((a.coordinates x).toAdd,(b.coordinates y).toAdd) = v
      rw [hx,hy]
      rfl
    kernel_eq := by
      ext z
      obtain ⟨⟨x,y⟩,rfl⟩ := hp z
      change f (p (x,y)) = 1 ↔ (x:G)*(y:G) ∈ Z
      rw [hf]
      constructor
      · intro hz
        have hx : a.coordinates x = 1 := congrArg (fun v => Multiplicative.ofAdd v.toAdd.1) hz
        have hy : b.coordinates y = 1 := congrArg (fun v => Multiplicative.ofAdd v.toAdd.2) hz
        exact Z.mul_mem ((a.coordinates_eq_one_iff x).mp hx) ((b.coordinates_eq_one_iff y).mp hy)
      · intro hz
        have hxB : (x:G) ∈ B := by
          simpa only [mul_inv_cancel_right] using B.mul_mem (b.kernel_le hz) (B.inv_mem y.property)
        have hxZ := hi ⟨x.property,hxB⟩
        have hyZ : (y:G) ∈ Z := by
          simpa only [inv_mul_cancel_left] using Z.mul_mem (Z.inv_mem hxZ) hz
        change Multiplicative.ofAdd ((a.coordinates x).toAdd,(b.coordinates y).toAdd) = 1
        rw [(a.coordinates_eq_one_iff x).mpr hxZ,(b.coordinates_eq_one_iff y).mpr hyZ]
        rfl
    equivariant := by
      intro h z
      obtain ⟨⟨x,y⟩,rfl⟩ := hp z
      let x' : A := ⟨(h:G)*x*(h:G)⁻¹,(a.normalized h.property x).mp x.property⟩
      let y' : B := ⟨(h:G)*y*(h:G)⁻¹,(b.normalized h.property y).mp y.property⟩
      have he : (⟨(h:G)*p (x,y)*(h:G)⁻¹,(hnorm h.property _).mp (p (x,y)).property⟩ : (A ⊔ B : Subgroup G)) = p (x',y') := by
        apply Subtype.ext
        change (h:G)*((x:G)*(y:G))*(h:G)⁻¹ =
          ((h:G)*(x:G)*(h:G)⁻¹)*((h:G)*(y:G)*(h:G)⁻¹)
        group
      rw [he,hf,hf]
      exact Prod.ext (a.equivariant h x) (b.equivariant h y) }
  refine ⟨d,hf,?_,?_⟩
  · intro z
    obtain ⟨⟨x,y⟩,rfl⟩ := hp z
    change (x:G)*(y:G) ∈ A ↔ (f (p (x,y))).toAdd.2 = 0
    rw [hf]
    change (x:G)*(y:G) ∈ A ↔ b.coordinates y = 1
    rw [b.coordinates_eq_one_iff]
    constructor
    · intro hz
      have hy : (y:G) ∈ A := by
        simpa only [inv_mul_cancel_left] using A.mul_mem (A.inv_mem x.property) hz
      exact hi ⟨hy,y.property⟩
    · intro hy
      exact A.mul_mem x.property (a.kernel_le hy)
  · intro z
    obtain ⟨⟨x,y⟩,rfl⟩ := hp z
    change (x:G)*(y:G) ∈ B ↔ (f (p (x,y))).toAdd.1 = 0
    rw [hf]
    change (x:G)*(y:G) ∈ B ↔ a.coordinates x = 1
    rw [a.coordinates_eq_one_iff]
    constructor
    · intro hz
      have hx : (x:G) ∈ B := by
        simpa only [mul_inv_cancel_right] using B.mul_mem hz (B.inv_mem y.property)
      exact hi ⟨x.property,hx⟩
    · intro hx
      exact B.mul_mem (b.kernel_le hx) y.property
end Representation.BinaryConjugationSection
