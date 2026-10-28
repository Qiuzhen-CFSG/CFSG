module

public import Theory.Representation.BinaryConjugationSection.IntersectedChiefFactor
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Flags

/-!
# Comparing sections with a relative kernel intersection

For literal sections S/R and P/C, only R ∩ P ≤ C is needed to compare
the coordinates on S ∩ P. Assuming C ≤ P, the resulting equivariant
surjection has kernel exactly the image of S ∩ C in S/R. The proof
retains both coordinate maps and does not assume R ≤ P or R ≤ C.

This is the relative-denominator version of `exists_intersection_intertwiner`.
Its original-group consumer is the second L₁-chief factor of S/R in
Aschbacher–Smith 14.7.24(1), printed p.1051, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G]

/-- Compare intersected sections using only the kernel's intersection with
the second numerator. The image of the second denominator is the exact kernel. -/
theorem exists_relative_intersection_intertwiner
    {J H A R V B N : Subgroup G} (hAJ : A ≤ J) (hAH : A ≤ H)
    {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {τ : Representation (ZMod 2) J X} {σ : Representation (ZMod 2) H Y}
    (s : BinaryConjugationSection J R V τ) (t : BinaryConjugationSection H B N σ)
    (hNB : N ≤ B) (hVN : V ⊓ B ≤ N)
    (D₀ D₁ : Subrepresentation (τ.comp (inclusion hAJ)))
    (D : Subrepresentation (σ.comp (inclusion hAH)))
    (h₀ : D₀.toSubmodule = s.imageSpace N) (h₁ : D₁.toSubmodule = s.imageSpace B)
    (hD : D.toSubmodule = t.imageSpace R) :
    ∃ f : D₁.toRepresentation.IntertwiningMap D.toRepresentation,
      Function.Surjective f ∧ ∀ x : D₁.toSubmodule, f x = 0 ↔ (x : X) ∈ D₀ := by
  let I := R ⊓ B
  let q : I →* Multiplicative D₁.toSubmodule := {
    toFun x := Multiplicative.ofAdd ⟨(s.coordinates ⟨x,x.property.1⟩).toAdd,
      h₁.symm ▸ (s.mem_imageSpace_iff B _).mpr ⟨⟨x,x.property.1⟩,x.property.2,rfl⟩⟩
    map_one' := by apply Subtype.ext; exact s.coordinates.map_one
    map_mul' x y := by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd
        (s.coordinates.map_mul ⟨x,x.property.1⟩ ⟨y,y.property.1⟩) }
  let r : I →* Multiplicative D.toSubmodule := {
    toFun x := Multiplicative.ofAdd ⟨(t.coordinates ⟨x,x.property.2⟩).toAdd,
      hD.symm ▸ (t.mem_imageSpace_iff R _).mpr ⟨⟨x,x.property.2⟩,x.property.1,rfl⟩⟩
    map_one' := by apply Subtype.ext; exact t.coordinates.map_one
    map_mul' x y := by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd
        (t.coordinates.map_mul ⟨x,x.property.2⟩ ⟨y,y.property.2⟩) }
  have hq : Function.Surjective q := by
    intro x
    have hx : x.toAdd.val ∈ s.imageSpace B := h₁.le x.toAdd.property
    obtain ⟨a,ha,he⟩ := (s.mem_imageSpace_iff B _).mp hx
    exact ⟨⟨a,a.property,ha⟩,Subtype.ext he⟩
  have hr : Function.Surjective r := by
    intro x
    have hx : x.toAdd.val ∈ t.imageSpace R := hD.le x.toAdd.property
    obtain ⟨a,ha,he⟩ := (t.mem_imageSpace_iff R _).mp hx
    exact ⟨⟨a,ha,a.property⟩,Subtype.ext he⟩
  have hk : q.ker ≤ r.ker := by
    intro x hx
    apply Subtype.ext
    apply (t.coordinates_eq_one_iff _).mpr
    apply hVN
    refine ⟨?_,x.property.2⟩
    apply (s.coordinates_eq_one_iff ⟨x,x.property.1⟩).mp
    exact congrArg (fun z : Multiplicative D₁.toSubmodule => (z.toAdd : X)) hx
  let f₀ := q.liftOfSurjective hq ⟨r,hk⟩
  have hf₀ (x : I) : f₀ (q x) = r x := q.liftOfRightInverse_comp_apply _ _ _ x
  let f : D₁.toSubmodule →ₗ[ZMod 2] D.toSubmodule :=
    (AddMonoidHom.toMultiplicative.symm f₀).toZModLinearMap 2
  have hf (x : I) : f (q x).toAdd = (r x).toAdd := hf₀ x
  have hequiv (a : A) (x : D₁.toSubmodule) :
      f (D₁.toRepresentation a x) = D.toRepresentation a (f x) := by
    obtain ⟨v,hv⟩ := hq (Multiplicative.ofAdd x)
    have hx : (q v).toAdd = x := congrArg Multiplicative.toAdd hv
    rw [←hx]
    let y : I := ⟨(a : G)*v*(a : G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized (hAJ a.property)) v).mp v.property.1,
      (mem_normalizer_iff.mp (t.normalized (hAH a.property)) v).mp v.property.2⟩
    have hqy : (q y).toAdd = D₁.toRepresentation a (q v).toAdd :=
      Subtype.ext (s.equivariant (inclusion hAJ a) ⟨v,v.property.1⟩)
    have hry : (r y).toAdd = D.toRepresentation a (r v).toAdd :=
      Subtype.ext (t.equivariant (inclusion hAH a) ⟨v,v.property.2⟩)
    rw [←hqy,hf,hf,hry]
  let f' : D₁.toRepresentation.IntertwiningMap D.toRepresentation :=
    ⟨f,fun a => LinearMap.ext (hequiv a)⟩
  refine ⟨f',?_,?_⟩
  · intro y
    obtain ⟨x,hx⟩ := hr (Multiplicative.ofAdd y)
    exact ⟨(q x).toAdd,(hf x).trans (congrArg Multiplicative.toAdd hx)⟩
  · intro x
    obtain ⟨a,ha⟩ := hq (Multiplicative.ofAdd x)
    have hx : (q a).toAdd = x := congrArg Multiplicative.toAdd ha
    rw [←hx]
    change f (q a).toAdd = 0 ↔ (q a).toAdd.val ∈ D₀.toSubmodule
    rw [hf,Subtype.ext_iff,h₀]
    change t.coordinates ⟨a,a.property.2⟩ = 1 ↔ _
    rw [t.coordinates_eq_one_iff]
    change (a : G) ∈ N ↔ (s.coordinates ⟨a,a.property.1⟩).toAdd ∈ s.imageSpace N
    constructor
    · intro haN
      exact (s.mem_imageSpace_iff N _).mpr ⟨⟨a,a.property.1⟩,haN,rfl⟩
    · intro hm
      obtain ⟨v,hv,he⟩ := (s.mem_imageSpace_iff N _).mp hm
      have hker : ((v⁻¹ * ⟨a,a.property.1⟩ : R) : G) ∈ V := by
        apply (s.coordinates_eq_one_iff _).mp
        rw [map_mul,map_inv,Multiplicative.toAdd.injective he,inv_mul_cancel]
      have hBN : ((v⁻¹ * ⟨a,a.property.1⟩ : R) : G) ∈ N :=
        hVN ⟨hker,B.mul_mem (B.inv_mem (hNB hv)) a.property.2⟩
      simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_cancel_left] using N.mul_mem hv hBN


end Representation.BinaryConjugationSection
